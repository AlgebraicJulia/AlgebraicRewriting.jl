module Algorithms 

using Catlab 
using ...CategoricalAlgebra.CSets: invert_iso, var_reference
using ...Rewrite.Migration: pres_hash

"""
Break an ACSet into connected components, represented as a coproduct and an 
isomorphism from the original ACSet into the colimit apex.
"""
function connected_acset_components(X::ACSet)
  isempty(X) && return (coproduct([X]), id(X))  # edge case
  S = acset_schema(X)
  g = Graph()
  # Part dict maps X indices to graph vertices, part lookup goes other way
  part_dict, part_lookup = Dict(), Pair{Symbol, Int}[]
  for o in types(S) 
    append!(part_lookup, [o => p for p in parts(X, o)])
    vs = add_vertices!(g, nparts(X, o))
    part_dict[o] = Dict(zip(parts(X, o), vs))
  end
  for (h, s, t) in homs(S)
    for p in parts(X, s)
      add_edge!(g, part_dict[s][p], part_dict[t][X[p, h]])
    end
  end
  for (h, s, t) in attrs(S)
    for p in parts(X, s)
      fp = X[p, h]
      if fp isa AttrVar
        add_edge!(g, part_dict[s][p], part_dict[t][fp.val])
      end
    end
  end

  ιs = map(enumerate(connected_components(g))) do (i, cc)
    d = Dict(o=>Int[] for o in types(S))
    for elem in cc
      (o, idx) = part_lookup[elem]
      push!(d[o], idx)
    end 
    comp = constructor(X)()
    copy_parts!(comp, X; d...)
    ACSetTransformation(comp, X; Dict(k=>k ∈ ob(S) ? v : AttrVar.(v) 
                                      for (k, v) in pairs(d))...)
  end |> Multicospan
  cp = coproduct(dom.(ιs))
  return (cp, invert_iso(universal(cp, ιs)))
end

"""
Find all partial maps from the pattern to the addition, with some restrictions:
1. *Something* must be mapped into the newly added material.
2. Anything in L incident to a part mapped onto newly added material must be 
   mapped to newly added material
"""
function compute_overlaps(L::ACSet, I_R::ACSetTransformation; monic=[],   
                          S=nothing)::Vector{Span}
  overlaps = Span[]
  for subobj in all_subobjects(L, S)
    abs_subobj = abstract_attributes(dom(subobj))

    function prnt(s,x::ACSet)
      println(s);
      show(stdout,"text/plain",x)
    end
    function prnt(s,x::ACSetTransformation)
      println(s)
      for (k,v) in pairs(components(x))
        println("\t$k: [$(join(string.(collect(v)), ","))]")
      end
    end
    prnt("dom(abs_subobj)", dom(abs_subobj))
    prnt("codom(I_R)", codom(I_R))
  
    for h in homomorphisms(dom(abs_subobj), codom(I_R); monic)
      lft = abs_subobj ⋅ subobj
      good_overlap(lft, h, I_R) && push!(overlaps, Span(lft, h))
    end
  end
  return overlaps
end

"""
        subobj
        O ↣ L
        ↓h
    I ↣ R

Subobject O is presumed to be abstract, i.e. has only (distinct) variables
"""
function good_overlap(subobj::ACSetTransformation, h::ACSetTransformation, 
                      I_R::ACSetTransformation)
  S = acset_schema(dom(h))
  L = codom(subobj)
  O = dom(subobj) # for "overlap"
  O == dom(h) || error("subobj + h should be a span")
  # Parts of O which assign parts of L to newly added material via partial map
  new_mat = Dict(k => Set{Int}() for k in types(S)) 

  for k in ob(S)
    for p in parts(O, k)
      h[k](p) ∈ collect(I_R[k]) || push!(new_mat[k], p)
    end
  end
  for k in attrtypes(S)
    for p in parts(O, k)
      Lₚ, Rₚ = subobj[k](AttrVar(p)), h[k](AttrVar(p))
      (Lₚ isa AttrVar || Lₚ == Rₚ) && push!(new_mat[k], p)
    end
  end
  all(isempty, values(new_mat)) && return false # fail condition 1
  L_new = Dict(map(collect(pairs(new_mat))) do (k, vs)
    k => Set(map(collect(vs)) do v 
      subobj[k](k ∈ ob(S) ? v : AttrVar(v))
    end)
  end)
  for k in ob(S)
    for p in setdiff(parts(L, k), collect(subobj[k])) # for all old material
      for (f, _, cd) in homs(S; from=k) # for all things old material depends on
        cd == k && continue # TODO can we do this kind of filtering for, e.g. DDS?
        L[p, f] ∈ L_new[cd] && return false # fail condition 2
      end
      for (f, _, cd) in attrs(S; from=k)
        L[p, f] isa AttrVar && L[p, f] ∈ L_new[cd] && return false
      end
    end
  end
  return true
end

"""
Goal: find overlaps between a negative application condition, N, and some 
current state of the world, X, such that we can efficiently check if something 
has been deleted generates a match by allowing it to satisfy the NAC. The data:

`u`: X ↢ X' (we are updating via some deletion)
`nac`: L → N

X and X' are big. L and N are small. X ∖ X' is small. 

Let η ↣ ~N be any subobject of ~N, the complement of N, which is our best 
approximation to N ∖ L. 

We want matches η -> X that send everything in L to something in X'. 
But *something* in η must map to something *not* in X'. We look at all matches 
and then filter. 

But we can do something more efficient than enumerating Hom(η, X), as we we need 
only generate matches into ~u (our best approximation to the part of X that got 
deleted, X ∖ X'). 

Thus, our process for finding overlaps requires only searching for morphisms  
between two things which are themselves pattern-sized.
"""
function nac_overlap(nac, update::ACSetTransformation)
  N = codom(nac)
  Ob = ob(acset_schema(N))
  L_parts_in_N = Dict(o=>Set(collect(nac.m[o])) for o in Ob)
  non_deleted_X_parts = Dict(o=>Set(collect(update[o])) for o in Ob)
  mostly_deleted_X = hom(~Subobject(update)) # the deleted stuff, and a bit more
  χ = dom(mostly_deleted_X)
  undeleted = Dict(map(Ob) do o 
    o => Set(filter(∈(non_deleted_X_parts[o]), parts(χ,o)))
  end)
  res = Set{Span}() # could there be duplicates using this method?
  for subobj in nac.subobj # η ↣ ~N
    η = dom(subobj)
    η_to_N = subobj ⋅ nac.m_complement
    predicates = Dict(map(Ob) do o 
      o => Dict([p => undeleted[o] for p in parts(η,o) 
                 if η_to_N[o](p) ∈ L_parts_in_N[o]])
    end)
    for h in homomorphisms(η, χ; predicates)
      found = false  # need to find *some* part of η not in L and not in X'
      η_to_X = h ⋅ mostly_deleted_X
      for o in Ob
        found && break
        for p in parts(η, o)
          found && break
          Np, Xp = η_to_N[o](p), η_to_X[o](p)
          found = Np ∉ L_parts_in_N[o] && Xp ∉ non_deleted_X_parts[o]
        end
      end
      found && push!(res, Span(η_to_N, η_to_X))
    end
  end
  return res
end 

"""
Given f: L->X and m: X' ↣ X, find the unique map L -> X' making the triangle 
commute, if it exists.

TODO rewrite with @comptime
"""
function pull_back(f::ACSetTransformation, m::ACSetTransformation
                  )::Union{ACSetTransformation, Nothing}
  L, X′ = dom.([m, f])
  comps, S = Dict(), acset_schema(L)
  for o in ob(S)
    vec = []
    for i in parts(L, o)
      pre = preimage(f[o], m[o](i))
      length(pre) == 1 || return nothing
      all(attrs(S; from=o)) do (atr, _, _)
        L[i, atr] isa AttrVar || L[i,atr] == X′[only(pre), atr]
      end || return nothing
      push!(vec, only(pre))
    end
    comps[o] = vec
  end
  # Check that attribute variables in L are mapped consistently
  # i.e. L->X' doesn't send the variable to two different values.
  for o in attrtypes(S)
    comps[o] = map(AttrVar.(parts(L, o))) do i 
      vals = Set()
      for (f, c, _) in attrs(S; to=o)
        for p in incident(L, i, f)
          push!(vals, X′[comps[c][p], f])
        end
      end
      return only(vals)
    end
  end
  ACSetTransformation(dom(m), dom(f); comps...)
end

"""Get the pairs for each component of the image and its component"""
partition_image(f::ACSetTransformation) = Dict(map(ob(acset_schema(dom(f)))) do o
  del,nondel = Set(parts(codom(f), o)), Set{Int}()
  for p in parts(dom(f), o) 
    push!(nondel, f[o](p))
    delete!(del, f[o](p))
  end
  o => (nondel, del)
end)

"""
Compute and cache the subobject classifier; reuse if already computed.
Some schemas have no finitely presentable subobject classifier. Return `nothing` 
in that case.
"""
function subobject_cache(T::Type, S=nothing; cache="cache")
  S = deattr(isnothing(S) ? Presentation(T) : S)
  T = AnonACSetType(Schema(S))
  name = joinpath(cache,"Ω_$(nameof(T))_$(pres_hash(S)).json")
  mkpath(cache)
  DNT = "Did not terminate"
  if isfile(name)
    read(name, String) == DNT && return nothing
    return read_json_acset(T, name)
  else 
    try 
      Ω = first(subobject_classifier(T, S))
      write_json_acset(Ω, name)
      return Ω  
    catch e 
      e isa ErrorException && e.msg[1:5] == "Sigma" || throw(e)
      open(name, "w") do file
        write(file, DNT)
      end
      return nothing
    end
  end
end

"""
Convert a morphism X → Ω into a subobject X'↣X, assuming that Ω was generated 
by Catlab's `subobject_classifier` function.
"""
function to_subobj(f::ACSetTransformation)
  Subobject(dom(f); Dict(map(collect(pairs(components(f)))) do (k, v)
    k => findall(==(1), collect(v))
  end)...)
end

"""Get all subobjects as monos into X"""
function all_subobjects(X::ACSet, S=nothing; cache="cache")
  Ω = subobject_cache(typeof(X), S; cache) 
  isnothing(Ω) && return hom.(subobject_graph(X)[2]) # compute the slow way
  S = isnothing(S) ? acset_schema(X) : Schema(S)
  X′ = typeof(Ω)()
  copy_parts!(X′, X)
  return map(homomorphisms(X′, Ω; alg=VMSearch())) do h
    f = hom(to_subobj(ACSetTransformation(X′, Ω; h...)))
    A = constructor(X)()
    copy_parts!(A, dom(f))
    h′ = Dict(o => get(components(f), o, []) for o in types(S))
    for (a, c, d) in attrs(S)
      for p in parts(A, c)
        set_subpart!(A, p, a, AttrVar(add_part!(A, d)))
        push!(h′[d], X[f[c](p), a])
      end
    end
    ACSetTransformation(A, X; h′...)
  end
end

""" Remove attributes from a schema """
function deattr(S::Presentation)
  S′ = Presentation(FreeSchema)
  for o in generators(S, :Ob) ∪ generators(S, :Hom)
    add_generator!(S′, o)
  end
  for (l, r) in equations(S)
    add_equation!(S′, l, r) # TODO filter equations that reference attrs!
  end
  return S′
end

"""
VarFunctions can both bind variables to concrete values or merge variables
together. Although the overall VarFunction is not monic if either of these
happens, it is only combinatorially non-monic if variables are merged together.
"""
function is_combinatorially_monic(f::ACSetTransformation) 
  S = acset_schema(dom(f))
  all(o -> is_monic(f[o]), ob(S)) || return false
  return all(attrtype(S)) do o 
    attrimg = filter(v -> v isa AttrVar, collect(f[o]))
    length(attrimg) == length(unique(attrimg))
  end
end
end # module
