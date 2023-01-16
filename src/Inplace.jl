module Inplace 
export simulate, pushout!, apply_rule!, pushout_complement!

using Catlab
using Catlab.CategoricalAlgebra, Catlab.Graphs

using DataStructures, Random

"""
This file contains resources for computing DPO rewriting on ACSets in place, 
i.e. computing pushouts and pushout complements without creating copies of 
the ACSet data structure. 
"""

"""
For now, rules are given as spans of ACSetTransformations, not `Rule` objects.
"""
function simulate(init::StructACSet, 
                  rules; # rule + probability pairs OR just a list of rules
                  n=100) # number of timesteps
  if rules[1] isa Span # the data given does not have relative probability data 
    rules = [r => 1.0 for r in rules]
  end

  # Process the relative probabilities
  r_probs = last.(rules)
  p_total = sum(r_probs)
  p_cumulative = cumsum(r_probs)./p_total

  # Apply rules
  state = deepcopy(init)
  for _ in 1:n
    rnd = rand()
    r = findfirst(x-> x > rnd, p_cumulative) # index of rule we are executing 
    state = apply_rule!(rules[r][1], state)
  end  
  return state
end

"""Randomly apply a DPO rewrite rule, mutating the state in place
"""
function apply_rule!(r::Span, state::StructACSet)
  match = homomorphism(codom(left(r)), state; random=true)
  new_I_G = pushout_complement!(left(r), match)
  new_R_G = pushout!(new_I_G, right(r)) # i.e. compute pushout
  return codom(new_R_G)
end 

"""
    l
  L ↩ I
m ↓   ↓ res
  G⌝↩ G'

Compute pushout complement via updating data of G in place.
A morphism from I is returned. The old match morphism m (and 
any other references to G) are now invalid.

The validity of this code is dependent on assuming "pop and swap"
deletion behavior of indices. When 

"""
function pushout_complement!(l::ACSetTransformation{S}, 
                             m::ACSetTransformation{S}) where S
  G = codom(m)
  new_m_components = Dict(map(ob(S)) do o 
    del = sort([m[o](p) for p in parts(codom(l), o) if isempty(preimage(l[o], p))])
    nondel = [p for p in parts(G,o) if p ∉ del]
    curr = 0
    new_comps = [i for i in parts(G,o)]
    for d in del 
      (_, high_ind) = findmax(new_comps)
      new_comps[high_ind] = new_comps[d]
      new_comps[d] = 0
    end 
    for d in del 
      rem_part!(G, o, d) 
    end 
    o => new_comps[collect(m[o])]
  end)
  return l ⋅ ACSetTransformation(dom(m), G; new_m_components...)
end

"""
     r
   I --> R
lm ↓     ↓ result
   G -->⌜G'
"""
function pushout!(lm::ACSetTransformation{S}, 
                  r::ACSetTransformation{S}) where S
  G, R = codom.([lm,r])
  I = dom(lm)
  r_comps, r_new = [Dict{Symbol,Vector{Int}}() for _ in 1:2]
  for o in ob(S) 
    # Compute eq classes
    #-------------------
    ng = nparts(G,o)
    eq = IntDisjointSets(ng+nparts(R,o))
    for i in parts(I,o)
      union!(eq, lm[o](i), ng+r[o](i))
    end

    # Analyze eq classes 
    #------------------
    # Each part has a root in the union-find structure
    rootvec = [find_root!(eq,i) for i in 1:length(eq)]
    # All roots (each associated with its own eq class)
    roots = unique(sort(rootvec))
    # Identify eq class index via the root value
    root_ind = Dict([v=>k for (k,v) in enumerate(roots)])
    # All elements of each equivalence class
    eq_classes = [findall(==(root), rootvec) for root in roots]
    # Rather than the root, the lowest index will be our real representative
    eq_reps = first.(eq_classes)
    # Map which sends part #i to its representative
    μ = [eq_reps[root_ind[r]] for r in rootvec]

    # apply merge 
    #------------
    # Redirect all incoming homs to point at representatives
    for h in homs(S; to=o, just_names=true)
      set_subpart!(G, h, μ[G[h]]) 
    end
    
    # Then we can safely delete the non-representatives
    for eq_c in eq_classes 
      rem_parts!(G, o, filter(<(ng), eq_c[2:end]))
    end 

    # Apply add 
    #----------
    r_new[o] = [rep - ng for rep in eq_reps if rep > ng]
    r_comps[o] = zeros(nparts(R,o))
    for r in parts(R,o)
      if μ[r+ng] <= ng 
        r_comps[o][r] = μ[r+ng]
      elseif r+ng ∈ eq_reps 
        ats = Dict([a => R[r, a] for a in attrs(S; from=o, just_names=true)])
        r_comps[o][r] = add_part!(G,o; ats...)
      else 
        r_comps[o][r] = r_comps[o][μ[r]-ng]
      end 
    end
  end
  # Add in the hom data for the newly added parts to G
  #---------------------------------------------------
  for o in ob(S)
    for n in r_new[o]
      for (h,_,cd) in homs(S; from=o)
        set_subpart!(G, r_comps[o][n], h, r_comps[cd][R[n,h]])
      end 
    end
  end 
  # Return map from R to newly-updated G
  return ACSetTransformation(R, G; r_comps...)
end

end # module 
