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
rewrite!(h::IHS, m::ACSetTransformation; kw...) = 
  rewrite!(h, m, h[only(incident(h, empty_profile(h), :profile)),:qrule]; kw...)

rewrite!(h::IHS, m::ACSetTransformation, f::ACSetTransformation; kw...) = 
  rewrite!(h, [m], only(states(h)), [f]; kw...)


rewrite!(h::IHS, m::Vector{<:ACSetTransformation}, 
         fs::Vector{<:ACSetTransformation}; kw...) = 
  rewrite!(h, m, only(states(h)), fs; kw...)

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
                          iᵣs::Vector{Int}; alt=false)
  # Check matches have the current state as their codom.
  allequal([state(h, iₛ), codom.(ms)...]) || error("Matches aren't into state")

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
      force(qL ⋅ mm) == force(m)
    end)
  end

  if alt # use experimental algorithm which only relies on adhesivity cube
    rewrite_bulk_monic_matches(h, ms′, iₛ, qs)
  else
    rewrite_monic_matches!(h, ms′, iₛ, qs) # algorithm with complements
  end
end

""" Compute the effect of a batch rewrite by putting the rules in parallel """
function apply_batch_rewrite(f_batch, matches)
  Σf, Σm = oplus(f_batch), copair(matches);
  ΣL, ΣR = coproduct.([dom.(f_batch),codom.(f_batch)])
  ΣΔ, Σr = pushout(Σm, Σf);
  (ΣL, ΣR, Σm, ΣΔ, Σr)
end

####################################
# Batch rewriting with complements #
####################################


"""
Loop over: 
- all patterns, X
- all decompositions of X ≅ X_old + ΣᵢXᵢ (subtasks which together cover X∖X_old)
- our possibilities for interactions applied rules and the ΣᵢXᵢ
"""
function rewrite_monic_matches!(h::IHS, matches::Vector{<:ACSetTransformation}, 
                                iₛ::Int, ruleapps::Vector{Int})

  args = apply_batch_rewrite(h[ruleapps, :qrule], matches)

  for pattern_cc_id in pattern_ccs(h)
    for subobj_id in subobjs(h, pattern_cc_id)
      is_epic(h[subobj_id, :subobj]) && continue # XOld≅X recovers old matches

      for decomp_id in decomps(h, subobj_id)
        colim, σ = h[decomp_id, :decomp_colim], h[decomp_id, :decomp_iso]
        d_elems = decomp_elems(h, decomp_id)
        inters = map(d_elems) do decomp_elem
          # all of the scenarios we should be prepared for
          vcat(map(enumerate(ruleapps)) do (i_app,rule_id)
            is = interactions(h, h[decomp_elem, :decomp_src], rule_id)
            tuple.(i_app, is)
          end...)
        end
        # a combo is a list of DecompElem => (RuleAppIdx × Interaction)
        for combo in reverse(collect.(Iterators.product(inters...)))
          for m in find_new_matches_combo!(h, subobj_id, args..., colim, combo)
            # Process results
            #----------------
            match = components(σ⋅m)
            iₘ = add_part!(h, :Match; match, match_state=iₛ, match_time=h[iₛ,:curr]+1)
            iₓ = add_part!(h, :CreatedMatch; created_match=iₘ)
            for (πDecomp,(_, πInteraction)) in zip(decomp_elems(h, decomp_id),combo) 
              add_part!(h, :DecompInteraction; match_interaction=iₓ, πDecomp, πInteraction)
            end
          end
        end
      end
    end
  end
  inc_curr!(h, iₛ)
  set_state!(h, iₛ, codom(last(args)))
end

"""
Find all new matches X → H assuming a particular subobject Xold ↣ X as living in 
the old graph G and a particular decomposition of the remainder of X into 
subtasks and assuming an assignment of rule applications from the batch update 
to the subtask they are supposed to address (given by `combo`).
"""
function find_new_matches_combo!(h::IHS, subobj_id::Int, ΣL, ΣR, Σm, ΣΔ, Σr,
                                 colim, combo::Vector{Tuple{Int,Int}})
  # can only use each rewrite once per DecompElem
  length(unique(first.(values(combo)))) == length(combo) || return [] 

  G = dom(ΣΔ)
  Old = dom(h[subobj_id, :subobj]) # assume f(Old) ⊆ Δ
  old_maps = map(combo) do (ruleapp_idx, interaction_id)
    comp_to_lᵢ = h[interaction_id, :iL]# :interactionL]
    comp_to_lᵢ ⋅ legs(ΣL)[ruleapp_idx] ⋅ Σm
  end

  # Get a map from the base A into the OLD graph
  constr = get_old_map_contraints(colim.diagram, old_maps)

  isnothing(constr) && return [] # unsatisfiable constraints

  new_maps = map(combo) do (ruleapp_idx, interaction_id) 
    comp_to_rᵢ = h[interaction_id, :iR]# :interactionR]
    comp_to_rᵢ ⋅ legs(ΣR)[ruleapp_idx] ⋅ Σr
  end

  map(homomorphisms(Old, G; initial=constr)) do m
    universal(colim, Multicospan([m ⋅ ΣΔ; new_maps]))
  end
end


##########################################
# Batch rewriting with adhesive property #
##########################################

"""
Loop over: 
- all patterns, X
- all decompositions of X ≅ X_old + ΣᵢXᵢ (subtasks which together cover X∖X_old)
- our possibilities for interactions applied rules and the ΣᵢXᵢ
"""
function rewrite_bulk_monic_matches(ihs::IHS, m::Vector{<:ACSetTransformation},
                                    iₛ::Int, ifs::Vector{Int})
  res, G, fs = [], ihs[iₛ, :state], ihs[ifs, :qrule]
  dom.(m) == dom.(fs) || error("Bad $(dom.(m)) \n\n $(dom.(fs))")
  ΣL, ΣR, Σm, ΣΔ, Σr = apply_batch_rewrite(fs, m)
  N = length(fs)
  N1 = N == 1 
  for iₚ in parts(ihs, :SubPattern)
    Old = ihs[iₚ, :subobj]
    Old_Comp = force(hom(~Subobject(Old)))
    pat_id = ihs[iₚ,:subpattern]
    other_ids = incident(ihs, pat_id, :subpattern)
    other_so = force.(ihs[other_ids, :subobj])
    Old_Comp_id = other_ids[findfirst(other_so) do so 
      any(isomorphisms(dom(so), dom(Old_Comp))) do σ
        force(σ ⋅ Old_Comp) == so
      end
    end]
    for d in incident(ihs, iₚ, :decomp_tgt2)
      # Colimit of the diagram : XR₁ ← XL₁ → XG ← XLₙ → XRₙ ...
      colim, σ = ihs[d, :decomp_colim2], ihs[d, :decomp_iso2]
      dom(σ) == codom(ihs[iₚ, :subobj]) || error("Bad")
      elems = incident(ihs, d, :decomp2)
      ND = length(elems)
      getindex.(Ref(ihs), elems, :decomp_elem_idx) == collect(1:ND) || error(
        "Decomp out of order!")
      LRs = map(elems) do elem 
        (ihs[elem, :decomp_elem_L], ihs[elem, :decomp_elem_R] )
      end
      OPTIMIZE = last.(LRs) == [Old_Comp_id]
      N1 && !OPTIMIZE && continue
      # assign a rule application to each component of the decomposition
      for combo in permutations(1:N,ND)
        # for each rule + decomp pair, consider all compatible interactions
        interactions = map(zip(LRs, combo)) do ((L,R), iᶠ)
          intersect(incident.(Ref(ihs), [L, R, ifs[iᶠ]], 
                              [:idata_L, :idata_R, :i_rule3])...)
        end
        for interaction_choice in Iterators.product(interactions...)
          get_runtime_matches(ihs, res, iₛ, G, m, ΣL, ΣR, Σm, ΣΔ, Σr, Old, 
                              colim, σ, combo, interaction_choice)
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
                             colim, σ, combo, interaction_choice)
  old_maps = map(zip(interaction_choice, combo, ob₁(colim.diagram))) do (int,iᶠ, XL)
    dom(ihs[int, :idata_iL] ) == XL || error("Unexpected domain")
    ihs[int, :idata_iL] ⋅ legs(ΣL)[iᶠ] ⋅ Σm
  end


  # Get a map from the base A into the OLD graph
  constr = get_old_map_contraints(colim.diagram, old_maps)

  isnothing(constr) && return
  isempty(dom(Old)) || all(isempty,values(constr)) && error("NO CONSTRAINTS")
  new_maps = map(zip(interaction_choice, combo)) do (int,iᶠ)
    ihs[int, :idata_iR] ⋅ legs(ΣR)[iᶠ] ⋅ Σr
  end

  hs = filter(homomorphisms(dom(Old), G; initial=constr)) do hg
    (length(m)==1) && return true 
    all(zip(interaction_choice, combo)) do (int, iᶠ)
      ι = subobj_incl(ihs[int, (:idata_L, :subobj)], Old) |> force
      hₗ = ihs[int, :idata_iL] |> force
      hₗ′,ι′= pb = pullback(m[iᶠ], hg)
      u′ = universal(pb, Span(hₗ, ι))
      is_epic(u′) && is_monic(u′) || return false
      force(u′⋅ι′) == ι && force(u′⋅hₗ′) == hₗ
    end
  end

  for h in hs
    u = universal(colim, Multicospan([compose(h, ΣΔ); new_maps]))
    push!(res, σ ⋅ u)
    match = components(σ ⋅ u)
    created_match3 = add_part!(ihs, :Match; match,match_state=iₛ, match_time=ihs[iₛ,:curr]+1 )
    matchdecomp_match = add_part!(ihs, :CreatedMatch3; created_match3)

    z = zip(interaction_choice, components.(new_maps))
    for (matchdecomp_interaction, matchdecomp_hom) in z
      add_part!(ihs, :MatchDecomp; matchdecomp_match, 
                matchdecomp_interaction, matchdecomp_hom)
    end
  end
end

end # module
