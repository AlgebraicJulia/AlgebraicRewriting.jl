module DPO 

using Catlab.CategoricalAlgebra

using ...CategoricalAlgebra.CSets
import ...CategoricalAlgebra.CSets: var_eqs
using ..Utils
import ..Utils: rewrite_match_maps, check_match_var_eqs

using DataStructures: find_root!

"""    rewrite_match_maps(r::Rule{:DPO}, m)
Apply a DPO rewrite rule (given as a span, L<-I->R) to a ACSet
using a match morphism `m` which indicates where to apply the rewrite.
              l   r
           L <- I -> R
         m ↓    ↓    ↓
           G <- K -> H

This works for any type that implements `pushout_complement` and `pushout`
"""
function rewrite_match_maps(r::Rule{:DPO}, m; check::Bool=false)
  if check
    can_pushout_complement(left(r), m) || error("Can't pushout complement $r\n$m")
  end
  ik, kg = pushout_complement(left(r), m)  
  rh, kh = pushout(right(r), ik) 
  Dict(:ik=>ik, :kg=>kg, :rh=>rh, :kh=>kh)
end

var_eqs(r::Rule{:DPO}, m::ACSetTransformation) = var_eqs(left(r), m)

"""
A match may be invalid because two variables (which are to be assigned different
values via the I -> R map) are identified (due to merging via the I->L map, 
which morally ought be monic but is not for AttrVars). We can check this before
computing the pushout to make sure that we will not get an inconsistent result 
when trying to compute it. This requires executing the custom exprs of the 
rewrite rule, so we may wish to build in the ability to skip this step if that 
is computationally intensive.
"""
function check_match_var_eqs(r::Rule{:DPO}, m::ACSetTransformation)
  eqs = var_eqs(r, m)
  I = dom(left(r))
  S = acset_schema(I)
  errs = []
  for at in attrtypes(S)
    roots = find_root!.(Ref(eqs[at]), 1:length(eqs[at]))
    for root in unique(roots)
      elems = findall(==(root), roots)
      if length(elems) > 1 # potential for conflict
        res = map(AttrVar.(elems)) do elem
          rval = right(r)[at](elem)
          rval isa AttrVar || return rval
          r.exprs[at][rval.val](collect(m[at]))
        end
        length(unique(res)) == 1 || push!(errs, "$at: inconsistent $elems↦$res")
      end
    end
  end
  return errs
end

"""Ignore for other categories"""
check_match_var_eqs(::Rule{:DPO}, m) = []

end # module 
