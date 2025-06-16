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
function rewrite_match_maps(r::Rule{:DPO}, m; cat, check::Bool=false)
  if check
    can_pushout_complement[cat](left(r), m) || error("Can't pushout complement $r\n$m")
  end
  ik, kg = pushout_complement[cat](left(r), m)  
  rh, kh = pushout[cat](right(r), ik) 
  Dict(:ik=>ik, :kg=>kg, :rh=>rh, :kh=>kh)
end

end # module 
