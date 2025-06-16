module CoNeg 
using Catlab.CategoricalAlgebra, GATlab

using ...CategoricalAlgebra.CSets
using ..Utils
import ..Utils: rewrite_match_maps
import Catlab.CategoricalAlgebra: Subobject

Subobject(X::ACSet, f::ACSetTransformation) = 
  Subobject(X; Dict([k=>collect(vs) for (k,vs) in pairs(components(f))])...)

"""    rewrite_match_maps(r::Rule{:CoNeg}, m)
Apply a CoNegation rewrite rule (given as a span, L↩I->R) to a ACSet
using a monic match morphism `m` which indicates where to apply the rewrite.
              l   r
           L <- I -> R
         m ↓    ↓    ↓
           G <- K -> H   where  K = ~L ∨ I

This works for any type that implements bi-Heyting logic operators ~ and ∨.

This is described [here](https://topos.site/blog/2023/04/conegation-rewriting).
Essentially, it is partway between DPO and SPO. Suppose the rule tries to delete
two things, one of which satisfies the dangling condition, the other violates it.
While DPO would fail to apply at all, and SPO would delete both things (cascading 
the deletion for the latter), co-negation rewriting would simply delete the item 
which can be deleted without cascading and ignore the other element.

It includes a quote which indicates that this method should work even when the 
match morphism isn't monic, if it satisfies the identification condition. 
Supporting this is not yet implemented.

Match morphisms which bind attribute variables are not monic, hence we this 
form of rewriting doesn't support VarACSets. Intuitively, it feels like this 
restriction could be relaxed.
"""
function rewrite_match_maps(r::Rule{:CoNeg}, m; cat, check::Bool=false)
  !check || is_monic(m) || error("Can only use CoNeg rewriting with monic matches: $m")
  L = codom[cat](m)
  L′ = Subobject(L, m)
  I′ = Subobject(L, compose[cat](left(r), m))
  K′ = @withmodel cat (~, ∨) begin 
    ~L′ ∨ I′
  end
  ik = hom(Subobject(dom[cat](hom(K′)), hom(I′)))
  rh, kh = pushout[cat](right(r), ik)
  Dict(:ik => ik, :kg => hom(K′), :rh => rh, :kh => kh)
end

end # module