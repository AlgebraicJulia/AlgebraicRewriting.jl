module DPO 
import ..Utils: rewrite_match_maps

using ..Utils
using ...CategoricalAlgebra.CSets
using Catlab.CategoricalAlgebra

"""    rewrite_match_maps(r::Rule{:DPO}, m)
Apply a DPO rewrite rule (given as a span, L<-I->R) to a ACSet
using a match morphism `m` which indicates where to apply
the rewrite.
              l   r
           L <- I -> R
         m ↓    ↓    ↓
           G <- K -> H

This works for any type that implements `pushout_complement` and `pushout`

Returns the morphisms I->K, K->G (produced by pushout complement), followed by
R->H, and K->H (produced by pushout)
"""
function rewrite_match_maps(r::Rule{:DPO}, m; check::Bool=false)
  if check
    err = "Cannot pushout complement $r\n$m"
    can_pushout_complement(ComposablePair(r.L, m)) || error(err)
  end
  ik, kg = pushout_complement(ComposablePair(r.L, m))  
  rh, kh = pushout(r.R, ik) 
  return Dict(:ik=>ik, :kg=>kg, :rh=>rh, :kh=>kh)
end

end # module 