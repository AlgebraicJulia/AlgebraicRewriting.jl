"""Incremental homomorphism search"""
module Incremental 
export IncHomSet, IncHomSets, rewrite!, matches

using ..Rewrite
using ..Rewrite.Utils: get_result, get_rmap, get_pmap
using ..CategoricalAlgebra.CSets: invert_iso

using StructEquality
using Catlab
using Catlab.CategoricalAlgebra.CSets: total_parts, ACSetColimit

# Data Structures 
#################
"""
Interface:
pattern(::IncHomSet) gets the domain ACSet of the hom set we are maintaining
state(::IncHomSet) gets the codomain ACSet of the hom set we are maintaining
matches(::IncHomSet) an iterator of morphisms in the hom set
"""
abstract type IncHomSet end

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
"""
struct IncCCHomSet <: IncHomSet
  pattern::ACSet
  additions::Vector{ACSetTransformation}
  overlaps::Vector{Vector{Span}}
  matches::Set{ACSetTransformation}
  state::Ref{<:ACSet}
  function IncCCHomSet(L, as, X)
    all(is_monic, as) || error("Nonmonic addition") # TODO: relax this condition
    new(L, as, compute_overlaps(L, as), Set(homomorphisms(L, X)), Ref(X))
  end
end

matches(h::IncCCHomSet) = h.matches
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
end

additions(h::IncSumHomSet) = additions(first(h.ihs))
state(h::IncSumHomSet) = state(first(h.ihs))

"""Universal property of coprod: induce map from pattern, given component maps"""
matches(h::IncSumHomSet) = map(Iterators.product(matches.(h.ihs)...)) do comps
  h.iso ⋅ universal(h.coprod, Multicospan(collect(comps)))
end

function IncHomSet(L::ACSet, additions::Vector{<:ACSetTransformation}, state::ACSet)
  coprod, iso = connected_acset_components(L)
  if length(coprod) == 1
    IncCCHomSet(L, additions, state)
  else 
    ihs = IncCCHomSet.(dom.(coprod.cocone), Ref(additions), Ref(state))
    IncSumHomSet(L, coprod, iso, ihs)
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
  e = elements(X)
  g = Graph(nparts(e, :El))
  Ob = e[:nameo]
  for (s,t) in zip(e[:src], e[:tgt]) # Delta migrate Elements to Graph
    add_edge!(g, s, t) 
  end
  ιs = map(enumerate(connected_components(g))) do (i, cc)
    d = Dict(o=>Int[] for o in Ob)
    for elem in cc
      o = e[elem, [:πₑ, :nameo]]
      push!(d[o], findfirst(==(elem), incident(e, e[elem, :πₑ], :πₑ)))
    end 
    comp = constructor(X)()
    copy_parts!(comp, X; d...)
    ACSetTransformation(comp, X; d...)
  end |> Multicospan
  cp = coproduct(dom.(ιs))
  (cp, invert_iso(universal(cp, ιs)))
end

"""
Find all overlaps between the pattern and each addition, restricting to only 
overlaps where a nonempty portion of the pattern intersects newly added material.
"""
function compute_overlaps(L::ACSet, as::Vector{<:ACSetTransformation}
                         )::Vector{Vector{Span}}
  map(as) do I_R
    overlaps = Span[]
    for subobj in hom.(subobject_graph(L)[2][1 : end-1]) # skip empty SubACSet
      if true # length(connected_acset_components(dom(subobj))[1]) == 1
        for h in homomorphisms(dom(subobj), codom(I_R))
          if !all(((k,v),) -> collect(v) ⊆ collect(I_R[k]), pairs(components(h)))
            push!(overlaps, Span(subobj, h))
          end
        end
      end
    end
    overlaps
  end
end

"""
Add to `matches` based on an addition #i specified via a pushout (rmap, update)

                 For all overlaps:  apex ↪ L
                                    ↓      ⇣ (find all of these!) 
 Hom(L, X_old) => Hom(L, X)         Rᵢ ⟶  X
                                    rmap ⌞ ↑ update
                                          X_old

However, we only want maps L → X whose *boundary* is completely outside of the 
image of Rᵢ. This is to avoid double-counting with a slightly bigger 
overlap which has already been calculated between L and Rᵢ.
"""
function addition!(hset::IncCCHomSet, i::Int, rmap::ACSetTransformation, 
                   update::ACSetTransformation)
  X, L, new_matches = codom(rmap), hset.pattern, []
  S = acset_schema(hset.pattern)
  old_matches = [m ⋅ update for m in hset.matches]  # Push forward old matches
  old_stuff = Dict(o => setdiff(parts(X,o), collect(rmap[o])) for o in ob(S))
  seen_constraints = Set() # if match is non-monic, different subobjects can be 
  for (DEBUG, (subL, mapR)) in enumerate(hset.overlaps[i])
    #println("OVERLAP $DEBUG")
    initial = Dict(map(ob(S)) do o  # initialize based on overlap btw L and R
      o => Dict(map(parts(dom(subL), o)) do idx
        subL[o](idx) => rmap[o](mapR[o](idx))  # make square commute
      end)
    end)
    #println("\tinitial $initial")
    if initial ∉ seen_constraints
      push!(seen_constraints, initial)
      L_image = Dict(o => Set(collect(subL[o])) for o in ob(S))
      boundary = Dict(k => setdiff(collect(v), L_image[k]) 
                      for (k, v) in pairs(components(~(¬Subobject(subL)))))
      # boundary = Dict(map(ob(S)) do o 
      #   o => filter(parts(X, o)) do p 
      #     p ∈ old_stuff[o] && any(homs(S; from=o)) do (f, _, o′)
      #       X[p ,f] ∉ old_stuff[o′]
      #     end
      #   end
      # end) 
      #println("\tboundary (old way) $boundary′\n\tboundary $boundary")
      valid = Dict(o => Dict(pₒ => old_stuff[o] for pₒ in boundary[o]) for o in ob(S))
      #println("\tvalid $valid")
      for h in homomorphisms(L, X; initial, valid)
        #h ∈ new_matches || println("\tMATCH $h")
        h ∈ new_matches ? error("Duplicating work $h") : push!(new_matches, h)
      end
    end
  end
  reset_matches!(hset, old_matches, new_matches)
  hset.state[] = X
end

"""
Delete / modify existing matches based on the target ACSet being permuted or 
reduced to a subobject. If a match touches upon something which is deleted, 
remove the match. Given X ↩ X′ we are updating Hom(L, X) => Hom(L, X′)
"""
function deletion!(hset::IncCCHomSet, f::ACSetTransformation)
  new_matches = Set{ACSetTransformation}()
  for m in hset.matches
    m′, f′ = pullback(f, m)
    if is_monic(f′) && is_epic(f′)
      updated = force(invert_iso(f′) ⋅ m′)
      push!(new_matches, updated)
    end
  end
  reset_matches!(hset, new_matches)
  hset.state[] = dom(f)
end

"""Use a rewrite rule to induce a deletion followed by an addition"""
rewrite!(hset::IncHomSet, r::Rule) = rewrite!(hset, r, get_match(r, state(hset)))

function rewrite!(hset::IncCCHomSet, r::Rule{T}, match::ACSetTransformation) where T
  isnothing(can_match(r, match)) || error("Bad match data")
  i = findfirst(==(right(r)), hset.additions) # RHS of rule must be an addition
  hset.state[] == codom(match)|| error("Codom mismatch for match $match")
  res = rewrite_match_maps(r, match)
  pl, pr = get_pmap(T, res)
  deletion!(hset, pl)
  addition!(hset, i, get_rmap(T, res), pr)
end

deletion!(hset::IncSumHomSet, f) = deletion!.(hset.ihs, Ref(f))
addition!(hset, i, rmap, pr) = addition!.(hset.ihs, i, Ref(rmap), Ref(pr))
rewrite!(hset::IncSumHomSet, r::Rule, match::ACSetTransformation) =
  rewrite!.(hset.ihs, Ref(r), Ref(match))


"""Determine if an IncCCHomSet is invalid. Throw error if so."""
function validate(hset::IncCCHomSet)::Bool
  all(is_natural, hset.matches) || error("Unnatural")
  all(==(hset.pattern), dom.(hset.matches)) || error("Bad dom")
  all(==(hset.state[]), codom.(hset.matches)) || error("Bad codom")
  ref = IncHomSet(hset.pattern, hset.additions, hset.state[])
  xtra = setdiff(hset.matches, ref.matches)
  missin = setdiff(ref.matches, hset.matches)
  isempty(xtra ∪ missin) || error("\n\textra $xtra \n\tmissing $missin")
end

function validate(hset::IncSumHomSet)::Bool
  fst = first(hset.ihs)
  all(==(additions(fst)), additions.(hset.ihs)) || error("Addns don't agree")
  all(==(state(fst)), state.(hset.ihs)) || error("States don't agree")
  dom(hset.iso) == apex(hset.coprod) || error("Bad iso domain")
  codom(hset.iso) == hset.pattern || error("Bad iso codomain")
  is_epic(hset.iso) && is_monic(hset.iso) || error("Iso not an iso")
  length(hset.ihs) == length(hset.coprod) || error("len(IHS) != len(CCS)")
  for (i, (h, hs)) in enumerate(zip(hset.coprod, hset.ihs))
    dom(h) == hs.pattern || error("Sub-IncHomSet $i mismatch pattern")
  end
  all(validate, hset.ihs) || error("Unnatural component IncrementalHomSet")
end

end # module
