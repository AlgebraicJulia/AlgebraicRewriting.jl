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
function compute_overlaps(L::ACSet, I_R::ACSetTransformation)::Vector{Span}
  overlaps = Span[]
  for subobj in hom.(subobject_graph(L)[2])
    abs_subobj = abstract_attributes(dom(subobj))
    for h in homomorphisms(dom(abs_subobj), codom(I_R))
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

end # module