"""
Maps into cokernels induce overlaps with R which hopefully are always 
subobjects of the pullback of new matches with R->G2.
"""
module IHSRewrite 
export rewrite_matches!

using StructEquality, DataStructures, Combinatorics
using Catlab, ACSets
using Catlab.CategoricalAlgebra.Chase: extend_morphism_constraints
import Catlab: dom, codom, compose

import ....Rewrite: rewrite!
using ..IHSData, ..IHSAccess, ..IHSModify
using ..IHSAccess: rule, pattern_ccs, pattern_cc, curr, subobjs, decomps, 
                   decomp_elems, interactions, empty_profile
using ..IHSModify: inc_curr!, set_state!, merge_profile, subobj_incl

# User-facing interface
#######################
""" 
Rewrite with a single match, presuming we have a single rule and a single 
state we are tracking. 
"""
rewrite!(h::IHS, m::ACSetTransformation; kw...) = 
  rewrite!(h, m, h[only(incident(h, empty_profile(h), :profile)),:qrule]; kw...)

""" 
Rewrite with a single match + rule pair, assuming we have just one state
we are tracking 
"""
rewrite!(h::IHS, m::ACSetTransformation, f::ACSetTransformation; kw...) = 
  rewrite!(h, [m], only(states(h)), [f]; kw...)

""" 
Rewrite with a list of match+rule pairs (provided as a pair of lists), assuming 
there is just one state we are tracking 
"""
rewrite!(h::IHS, m::Vector{<:ACSetTransformation}, 
         fs::Vector{<:ACSetTransformation}; kw...) = 
  rewrite!(h, m, only(states(h)), fs; kw...)

""" Apply a batch rewrite to a particular state """
rewrite!(h::IHS, m::Vector{<:ACSetTransformation}, iₛ::Int, 
         fs::Vector{<:ACSetTransformation}; kw...) = 
  rewrite_matches!(h, m, iₛ, [rule(h, f) for f in fs]; kw...)

####################
# Helper functions #
####################

"""
Given a diagram with overlaps between the old material in X and all of the 
complements of the decomposition, produce some constraints for incremental hom 
search (if any such constraints are possible). These constraints are induced 
by forcing the diagram to commute when applying the universal property with 
found morphisms along with the induced morphisms from each complement (which are 
fixed).
"""
function get_old_map_contraints(bpd::BipartiteFreeDiagram, 
                                fs::AbstractVector{<:ACSetTransformation})
  to_old_data = map(incident(bpd, 1, :tgt)) do e 
    s = src(bpd, e)
    other = only(setdiff(incident(bpd, s, :src), [e]))
    (hom(bpd, e), tgt(bpd, other)-1)
  end
  old = ob₂(bpd, 1)
  Ob = ob(acset_schema(old))
  initial = Dict{Symbol, Dict{Int,Int}}()
  for k in Ob
    initial[k] = Dict{Int,Int}()
    for v in parts(old, k)
      for (f_old,  i_new) in to_old_data 
        v_intersect = preimage(f_old[k], v)
        isempty(v_intersect) && continue
        val = (fs[i_new])[k](only(v_intersect))
        if haskey(initial[k], v)
          initial[k][v] == val || return nothing # unsatisfiable
        else 
          initial[k][v] = val
        end
      end
    end
  end
  initial
end

"""
Quotient the rewrite rules Lᵢ↣Rᵢ via the matches mᵢ in order to get 
rules, qLᵢ↣qRᵢ, which are equivalent when applied with a monic match.

`iᵣs` is a vector of rule IDs (for the unquotiented rules, Lᵢ↣Rᵢ)
"""
function rewrite_matches!(h::IHS, ms::Vector{<:ACSetTransformation}, iₛ::Int, 
                          iᵣs::Vector{Int})
  # Check matches have the current state as their codom.
  allequal([state(h, iₛ), codom.(ms)...]) || error("Matches aren't into state")

  cat = infer_acset_cat(first(ms))

  # Look up quotiented rules in database (return the QRule ids) 
  qs = map(zip(ms, iᵣs)) do (m, iᵣ)
    only(incident(h, iᵣ, :rule) ∩ incident(h, merge_profile(m), :profile))
  end
  qLs = h[qs, :l_quot] # map Lᵢ ↠ qLᵢ

  # check that the map from L
  all(((qL,m),)->dom(qL) == dom(m), zip(qLs, ms)) || error("Bad qLs")

  # The new matches are the unique maps qLᵢ↣G to make triangle commute  
  ms′ = map(zip(qLs,ms)) do (qL, m) 
    only(filter(homomorphisms(codom(qL), codom(m))) do mm 
      compose[cat](qL, mm) ≃ force(m)
    end)
  end

  rewrite_bulk_monic_matches(h, ms′, iₛ, qs)
end

""" Compute the effect of a batch rewrite by putting the rules in parallel """
function apply_batch_rewrite(f_batch, matches)
  cat = infer_acset_cat(first(matches))
  tcat = TypedCatWithCoproducts(cat)
  𝒞, T𝒞 = WithModel(cat), WithModel(tcat) 
  Σf, Σm = oplus(T𝒞, f_batch), copair(T𝒞, matches);
  ΣL = coproduct(𝒞, dom.(f_batch)...)
  ΣR = coproduct(𝒞, codom.(f_batch)...)
  ΣΔ, Σr = pushout(𝒞, Σm, Σf);
  (ΣL, ΣR, Σm, ΣΔ, Σr)
end

##########################################
# Batch rewriting with adhesive property #
##########################################

"""
Loop over: 
- all patterns, X
- all decompositions of X ≅ X_old + ΣᵢXᵢ (subtasks which together cover X∖X_old)
- our possibilities for interactions applied rules and the ΣᵢXᵢ

We can `optimize` by filtering to only consider decompositions where:
                      XRᵢ = ~ (XG Vᵢ XRⱼ) (for j ≠ i)
In which case, `get_runtime_matches` is told to NOT filter via a pullback 
constraint. 

"""
function rewrite_bulk_monic_matches(ihs::IHS, m::Vector{<:ACSetTransformation},
                                    iₛ::Int, ifs::Vector{Int})
  res, G, fs = [], ihs[iₛ, :state], ihs[ifs, :qrule]
  dom.(m) == dom.(fs) || error("Bad $(dom.(m)) \n\n $(dom.(fs))")
  ΣL, ΣR, Σm, ΣΔ, Σr = apply_batch_rewrite(fs, m)
  N = length(fs)

  add_part!(ihs, :Update; update_state=iₛ, update_time=ihs[iₛ,:curr]+1, update_comp=components(ΣΔ))

  for iₚ in parts(ihs, :SubPattern)
    Old = ihs[iₚ, :subobj]
    for d in incident(ihs, iₚ, :decomp_tgt)
      # Colimit of the diagram : XR₁ ← XL₁ → XG ← XLₙ → XRₙ ...
      colim, σ = ihs[d, :decomp_colim], ihs[d, :decomp_iso]
      dom(σ) == codom(ihs[iₚ, :subobj]) || error("Bad")
      elems = incident(ihs, d, :decomp)
      ND = length(elems)
      getindex.(Ref(ihs), elems, :decomp_elem_idx) == collect(1:ND) || error(
        "Decomp out of order!")
      LRs = map(elems) do elem 
        (ihs[elem, :decomp_elem_L], ihs[elem, :decomp_elem_R] )
      end
      N < ND && continue # ignore decompositions that require too many rules

      # assign a rule application to each component of the decomposition
      for combo in permutations(1:N,ND)
        # for each rule + decomp pair, consider all compatible interactions
        interactions = map(zip(LRs, combo)) do ((L,R), iᶠ)
          intersect(incident.(Ref(ihs), [L, R, ifs[iᶠ]], 
                              [:idata_L, :idata_R, :i_rule])...)
        end
        for interaction_choice in Iterators.product(interactions...)
          get_runtime_matches(ihs, res, iₛ, G, m, ΣL, ΣR, Σm, ΣΔ, Σr, Old, 
                              colim, σ, combo, interaction_choice, d)
        end
      end
    end
  end
  inc_curr!(ihs, iₛ) # increment state's event counter
  set_state!(ihs, iₛ, codom(Σr)) # update the IHS state to result of rewrite
  ΣΔ, codom(ΣΔ), res # return extensional update map, new state, new matches
end

"""
Input is a decomposition of X into XG↣X (the old part of pattern X which lives 
over G) and other components Xₗᵢ↣ Xᵣᵢ, and given an assignment of particular 
rule applications in the batch update to these Xₗᵢ↣ Xᵣᵢ which putatively add 
the required data in order to generate a new match.

Given this data we find hg:XG → G s.t., for each commutative cube face:
  
    XLᵢ⌟↣ XRᵢ                    XLᵢ⌟↣ XG
  hₗᵢ ↓    ↓ hᵣᵢ  we have that  hₗᵢ ↓   ↓ hg
     Lᵢ ↣ Rᵢ                      Lᵢ ↣ G
        f                            mᵢ  

This pullback condition is tantamount to saying that 
elements in XG that are in the image of XL are determined
by making the commutative cube commute (so they are fixed 
during hom search). 

We current restrict hg to be a commutative square
we initial=constr, and then filter by those which form pullback
squares with all the rules.
"""
function get_runtime_matches(ihs, res, iₛ, G, m, ΣL, ΣR, Σm, ΣΔ, Σr, Old, 
                             colim, σ, combo, interaction_choice, matchdecomp)
  bpfd = getvalue(colim.diagram)
  cat = infer_acset_cat(Σm)
  𝒞 = WithModel(cat)
  bpfd isa BipartiteFreeDiagram || error("Unexpected diagram")
  old_maps = map(zip(interaction_choice, combo, ob₁(bpfd))) do (int,iᶠ, XL)
    XL′ = dom(ihs[int, :idata_iL] )
    XL′ == XL  || error("Unexpected domain $XL′ \n≠\n $XL")
    @withmodel cat (⋅) begin 
      ihs[int, :idata_iL] ⋅ legs(ΣL)[iᶠ] ⋅ Σm
    end
  end

  # Get a map from the base A into the OLD graph
  constr = get_old_map_contraints(bpfd, old_maps)

  isnothing(constr) && return
  isempty(dom(Old)) || all(isempty,values(constr)) && error("NO CONSTRAINTS")
  new_maps = map(zip(interaction_choice, combo)) do (int,iᶠ)
    @withmodel cat (⋅) begin 
      ihs[int, :idata_iR] ⋅ legs(ΣR)[iᶠ] ⋅ Σr
    end
  end

  hs = homomorphisms(dom(Old), G; initial=constr)

  for h in hs
    u = universal[cat](colim, Multicospan([compose[cat](h, ΣΔ); new_maps]))
    push!(res, compose[cat](σ, u))
    match = components(force(compose[cat](σ, u)))
    created_match = add_part!(ihs, :Match; match,match_state=iₛ, match_time=ihs[iₛ,:curr]+1 )
    matchdecomp_match = add_part!(ihs, :CreatedMatch; created_match)

    z = zip(interaction_choice, components.(new_maps))
    for (matchdecomp_interaction, matchdecomp_hom) in z
      add_part!(ihs, :MatchDecomp; matchdecomp_match, matchdecomp,
                matchdecomp_interaction, matchdecomp_hom)
    end
  end
end

end # module
