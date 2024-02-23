"""Incremental homomorphism search"""
module Incremental 
export IncHomSet, IncHomSets, rewrite!, matches

using ..Rewrite
using ..Rewrite.Utils: get_result, get_rmap, get_pmap, get_expr_binding_map
using ..CategoricalAlgebra.CSets: invert_iso
import ..Rewrite: rewrite!

using StructEquality
using Catlab
import Catlab: universal
using Catlab.CategoricalAlgebra.CSets: ACSetColimit
using Catlab.CategoricalAlgebra.HomSearch: total_parts

# Data Structures 
#################
"""
Interface:
pattern(::IncHomSet) gets the domain ACSet of the hom set we are maintaining
state(::IncHomSet) gets the codomain ACSet of the hom set we are maintaining
matches(::IncHomSet) an iterator of morphisms in the hom set
"""
abstract type IncHomSet end

matches(h::IncHomSet) = [h[k] for k in keys(h)]
pattern(h::IncHomSet) = h.pattern

"""
A hom-set, `matches`, `pattern` -> `state`, which is incrementally updated with 
respect to a class of changes to `state`. The pattern must be a single connected 
component.

The state, X, can be changed via restriction to subobjects and by pushout with 
any of the predeclared monic `additions`. 

                              additionⱼ
                            • >--------> Rⱼ
                            ↓          ⌜ ↓
                            X ---------> X′

Cached `overlaps` data helps compute how the hom set updates with respect to a 
given addition being applied. The cache records in element i data for when we 
are updating the hom set after having applied addition i. It stores 
partial overlaps between L and Rᵢ which have *some* data that hits upon the 
new content added.

This is currently designed to work with DenseParts ACSets but could be 
straightforwardly modified to work with MarkAsDeleted ACSets, which would be 
even more efficient.

TODO: there should be a data structure for just a single addition and then 
a structure for multiple additions (which share the same pattern).
"""
struct IncCCHomSet <: IncHomSet
  pattern::ACSet
  additions::Vector{ACSetTransformation}
  overlaps::Vector{Vector{Span}}
  match_vect::Vector{Dict{Int, ACSetTransformation}}
  key_vect::Vector{Pair{Int,Int}}
  key_dict::Dict{Pair{Int,Int}, Int}
  state::Ref{<:ACSet}
  function IncCCHomSet(L, as, X)
    all(is_monic, as) || error("Nonmonic addition") # TODO: relax this condition
    homs = homomorphisms(L, X)
    n = length(homs)
    key_vect = Pair{Int,Int}[1 => i for i in 1:n]
    key_dict = Dict{Pair{Int,Int},Int}((1 => i) => i for i in 1:n)
    new(L, as, compute_overlaps.(Ref(L), as), [Dict(enumerate(homs))], 
        key_vect, key_dict, Ref(X))
  end
end

Base.length(i::IncCCHomSet) = length(match_vect(i))
Base.getindex(i::IncCCHomSet, ij::Pair{Int,Int}) = i.match_vect[ij[1]][ij[2]]
Base.getindex(i::IncCCHomSet, idx::Int) = i[i.key_vect[idx]]
Base.keys(h::IncCCHomSet) = keys(h.key_dict)

match_vect(h::IncCCHomSet) = h.match_vect
state(h::IncCCHomSet) = h.state[]
additions(h::IncCCHomSet) = h.additions

function reset_matches!(hset::IncCCHomSet, xs...)
  empty!(hset.matches)
  union!(hset.matches, xs...)
end

"""An incremental Hom Set for a pattern made of distinct connected components"""
struct IncSumHomSet <: IncHomSet
  pattern::ACSet
  coprod::ACSetColimit
  iso::ACSetTransformation # apex(coprod) ≅ pattern
  ihs::Vector{IncCCHomSet}
  key_vect::Vector{Vector{Pair{Int,Int}}}
  key_dict::Dict{Vector{Pair{Int,Int}}, Int}
end

"""WARNING one might also expect length to refer to the length of ihs"""
Base.length(h::IncSumHomSet) = length(first(h))

Base.getindex(h::IncSumHomSet, idxs::Vector{Pair{Int,Int}}) =
  universal(h, [hset[idx] for (hset, idx) in zip(h.ihs, idxs)])

Base.first(h::IncSumHomSet) = first(h.ihs)
Base.keys(h::IncSumHomSet) = 
  vec(collect.(collect(Iterators.product(keys.(h.ihs)...))))

additions(h::IncSumHomSet) = additions(first(h))
state(h::IncSumHomSet) = state(first(h))

"""Universal property of coprod: induce map from pattern, given component maps"""
matches(h::IncSumHomSet) = universal.(Ref(h), collect.(Iterators.product(matches.(h.ihs)...)))

"""Apply universal property and the isomorphism"""
universal(h::IncSumHomSet, comps::Vector{<:ACSetTransformation}) = 
  h.iso ⋅ universal(h.coprod, Multicospan(collect(comps)))

"""
`single` keyword forces the pattern to be treated as a single connected 
component, even if it's not
"""
function IncHomSet(L::ACSet, additions::Vector{<:ACSetTransformation}, state::ACSet; single=false)
  coprod, iso = connected_acset_components(L)
  if single || length(coprod) == 1
    IncCCHomSet(L, additions, state)
  else 
    ihs = IncCCHomSet.(dom.(coprod.cocone), Ref(additions), Ref(state))
    key_vect = Vector{Pair{Int,Int}}[]
    key_dict = Dict{Vector{Pair{Int,Int}}, Int}()
    IncSumHomSet(L, coprod, iso, ihs, key_vect, key_dict)
  end
end

# Algorithms 
############

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
    append!(part_lookup, [o=>p for p in parts(X, o)])
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
  (cp, invert_iso(universal(cp, ιs)))
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
  overlaps
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
  true
end

"""
Add to `matches` based on an addition #i specified via a pushout (rmap, update)

                 For all overlaps:  apex ↪ L
                                    ↓      ⇣ (find all of these!) 
 Hom(L, X_old) => Hom(L, X)         Rᵢ ⟶  X
                                    rmap ⌞ ↑ update
                                          X_old

However, we only want maps L → X where elements not in the image of L are all 
sent to X elements which outside of the image of rmap.

This is to avoid double-counting with a slightly bigger 
overlap which has already been calculated between L and Rᵢ.
"""
function addition!(hset::IncCCHomSet, i::Int, rmap::ACSetTransformation, 
                   update::ACSetTransformation)
  S = acset_schema(hset.pattern)
  # Push forward old matches
  for idx in 1:length(hset)
    hset.match_vect[idx] = Dict(
      k => m ⋅ update for (k, m) in pairs(hset.match_vect[idx]))
  end

  # Find newly-introduced matches
  X, L, new_matches, new_keys = codom(rmap), hset.pattern, Dict{Int, ACSetTransformation}(), Pair{Int,Int}[]

  push!(hset.match_vect, new_matches)
  old_stuff = Dict(o => setdiff(parts(X,o), collect(rmap[o])) for o in ob(S))
  seen_constraints = Set() # if match is non-monic, different subobjects can be identified
  for (idx, (subL, mapR)) in enumerate(hset.overlaps[i])
    initial = Dict(map(ob(S)) do o  # initialize based on overlap btw L and R
      o => Dict(map(parts(dom(subL), o)) do idx
        subL[o](idx) => rmap[o](mapR[o](idx))  # make square commute
      end)
    end)
    if initial ∉ seen_constraints
      push!(seen_constraints, initial)
      L_image = Dict(o => Set(collect(subL[o])) for o in ob(S))
      boundary = Dict(k => setdiff(parts(L,k), L_image[k]) for k in ob(S))
      predicates = Dict(o => Dict(pₒ => old_stuff[o] for pₒ in boundary[o]) 
                        for o in ob(S))
      for h in homomorphisms(L, X; initial, predicates)
        if h ∈ values(new_matches)
          error("Duplicating work $h") 
        else 
          # @info "NEW from $subL\n$mapR"
          new_key = length(hset) => length(new_keys)+1
          push!(hset.key_vect, new_key)
          push!(new_keys, new_key)
          hset.key_dict[new_key] = length(hset.key_vect)
          new_matches[length(new_keys)] = h 
        end
      end
    end
  end
  hset.state[] = X
  new_keys
end

"""
Delete / modify existing matches based on the target ACSet being permuted or 
reduced to a subobject. If a match touches upon something which is deleted, 
remove the match. Given X ↩ X′ we are updating Hom(L, X) => Hom(L, X′)
"""
function deletion!(hset::IncCCHomSet, f::ACSetTransformation)
  deleted = Pair{Int,Int}[]
  for (idx, dic) in enumerate(hset.match_vect)
    for (idx′, m) in collect(dic)
      m′ = pull_back(f, m)
      if isnothing(m′)
        delete!(dic, idx′)
        delete!(hset.key_dict, idx=>idx′)
        push!(deleted, idx=>idx′)
      else 
        dic[idx′] = m′
      end
    end
  end
  hset.state[] = dom(f)
  deleted
end

function pull_back(f::ACSetTransformation, m::ACSetTransformation)::Union{ACSetTransformation, Nothing}
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

"""Use a rewrite rule to induce a deletion followed by an addition"""
rewrite!(hset::IncHomSet, r::Rule) = rewrite!(hset, r, get_match(r, state(hset)))

function rewrite!(hset::IncCCHomSet, r::Rule{T}, match::ACSetTransformation) where T
  isnothing(can_match(r, match)) || error("Bad match data")
  i = findfirst(==(right(r)), hset.additions) # RHS of rule must be an addition
  hset.state[] == codom(match)|| error("Codom mismatch for match $match")
  res = rewrite_match_maps(r, match)
  pl, pr = get_pmap(T, res)
  x = get_expr_binding_map(r, match, res)
  pr′, rmap = (pr ⋅ x), (get_rmap(T, res) ⋅ x)
  deletion!(hset, pl)
  addition!(hset, i, rmap, pr′)
end

"""Perform a pushout addition given a match morphism from the domain."""
addition!(hset, i::Int, omap::ACSetTransformation) =
  addition!(hset, i, pushout(hset.additions[i], omap)...)

# Extending mutation methods to sums of connected components 
#-----------------------------------------------------------
deletion!(hset::IncSumHomSet, f) = deletion!.(hset.ihs, Ref(f))

addition!(hset::IncSumHomSet, i::Int, rmap::ACSetTransformation, pr::ACSetTransformation) = 
  addition!.(hset.ihs, i, Ref(rmap), Ref(pr))

rewrite!(hset::IncSumHomSet, r::Rule, match::ACSetTransformation) =
  rewrite!.(hset.ihs, Ref(r), Ref(match))

# Validation
############

"""Determine if an IncCCHomSet is invalid. Throw error if so."""
function validate(hset::IncCCHomSet)::Bool
  ms = matches(hset)
  all(is_natural, ms) || error("Unnatural")
  all(==(hset.pattern), dom.(ms)) || error("Bad dom")
  all(==(hset.state[]), codom.(ms)) || error("Bad codom")
  ref = IncHomSet(hset.pattern, hset.additions, hset.state[])
  xtra = setdiff(ms, values(first(match_vect(ref))))
  missin = setdiff(values(first(match_vect(ref))), ms)
  isempty(xtra ∪ missin) || error("\n\textra $xtra \n\tmissing $missin")
end

function validate(hset::IncSumHomSet)::Bool
  allequal(additions.(hset.ihs)) || error("Addns don't agree")
  allequal(state.(hset.ihs)) || error("States don't agree")
  allequal(length.(hset.ihs)) || error("Lengths don't agree")
  codom(hset.iso) == apex(hset.coprod) || error("Bad iso codomain")
  dom(hset.iso) == hset.pattern || error("Bad iso domain")
  is_epic(hset.iso) && is_monic(hset.iso) || error("Iso not an iso")
  length(hset.ihs) == length(hset.coprod) || error("len(IHS) != len(CCS)")
  for (i, (h, hs)) in enumerate(zip(hset.coprod, hset.ihs))
    dom(h) == hs.pattern || error("Sub-IncHomSet $i mismatch pattern")
  end
  all(validate, hset.ihs) || error("Unnatural component IncrementalHomSet")
end

end # module
