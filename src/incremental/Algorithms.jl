module Algorithms 

using Catlab 
using ...CategoricalAlgebra.CSets: invert_iso

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
1. Something must be mapped into the newly added material.
2. Anything in L incident to a part mapped onto newly added material must be 
   mapped to newly added material
"""
function compute_overlaps(L::ACSet, I_R::ACSetTransformation; monic=[])::Vector{Span}
  overlaps = Span[]
  for subobj in hom.(subobject_graph(L)[2])
    abs_subobj = abstract_attributes(dom(subobj))
    for h in homomorphisms(dom(abs_subobj), codom(I_R); monic)
      lft = abs_subobj ⋅ subobj
      good_overlap(lft, h, I_R) && push!(overlaps, Span(lft, h))
    end
  end
  return overlaps
end

function good_overlap(subobj::ACSetTransformation, h::ACSetTransformation, 
                      I_R::ACSetTransformation)
  S = acset_schema(dom(h))
  L = codom(subobj)
  # Parts of L which are mapped to newly added material via partial map
  new_mat = Dict(k=>Set{Int}() for k in types(S)) 
  for k in ob(S)
    for i in parts(dom(h), k)
      hᵢ = h[k](i)
      if hᵢ ∉ collect(I_R[k])
        push!(new_mat[k], subobj[k](i))
      end
    end
  end
  for k in attrtypes(S)
    for i in AttrVar.(parts(dom(h), k))
      hᵢ = h[k](i)
      if hᵢ isa AttrVar && subobj[k](i) isa AttrVar && hᵢ.val ∉ collect(I_R[k])
        push!(new_mat[k], subobj[k](i).val)
      end
    end
  end
  all(isempty, values(new_mat)) && return false # fail condition 1
  for k in ob(S)
    for p in setdiff(parts(L, k), collect(subobj[k]))
      for (f, _, cd) in homs(S; from=k)
        cd == k && continue # see comment in docstring about DDS
        L[p, f] ∈ new_mat[cd] && return false # fail condition 2
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
      push!(vec, only(pre))
    end
    comps[o] = vec
  end
  for o in attrtypes(S)
    comps[o] = map(AttrVar.(parts(L, o))) do i 
      for (f, c, _) in attrs(S; to=o)
        inc = incident(L, i, f)
        isempty(inc) || return X′[comps[c][first(inc)], f]
      end
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

end # module