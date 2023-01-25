module SPO 
import ..Utils: rewrite_match_maps

using ..Utils
using ...CategoricalAlgebra.CSets: var_pullback
using Catlab.CategoricalAlgebra


# Single-pushout rewriting
##########################

"""
  f         f
A ↣ B     A ↣ B
    ↓ g   ↓   ↓ g
    C     D ↣ C

Pullback complement where there first morphism is a mono.

Define D to be Im(g) to make it the largest possible subset of C such that we
can get a pullback.
"""
function pullback_complement(f, g)
  is_monic(f) || error("can only take pullback complement if f is mono")
  A = dom(f)
  d_to_c = hom(¬g(¬f(A))) # why isn't this just g(B)?
  # force square to commute by looking for the index in D making it commute
  ad = Dict(map(collect(pairs(components(compose(f,g))))) do (cmp, fg_as)
    cmp => Vector{Int}(map(collect(fg_as)) do fg_a
      findfirst(==(fg_a), collect(d_to_c[cmp]))
    end)
  end)
  return CSetTransformation(A, dom(d_to_c); ad...) => d_to_c
end

"""    rewrite_match_maps(r::Rule{:SPO}, ac)
NOTE: In the following diagram, a double arrow indicates a monic arrow.

We start with two partial morphisms, construct M by pullback, then N & O by
pullback complement, then finally D by pushout.


A ⇇ K → B         A ⇇ K → B
⇈                 ⇈ ⌟ ⇈ ⌞ ⇈
L          ⭆      L ⇇ M → N
↓                 ↓ ⌞ ↓ ⌜ ↓
C                 C ⇇ O → D

We assume the input A→C is total, whereas A→B may be partial, so it is given
as a monic K↣A and K→B.

Specified in Fig 6 of:
"Graph rewriting in some categories of partial morphisms"
"""
function rewrite_match_maps(r::Rule{:SPO}, ac)
  ka, kb = r.L, r.R
  e = "SPO rule is not a partial morphism. Left leg not monic."
  is_monic(ka) || error(e)

  lc, la = ac, id(dom(ac))
  ml, mk = pullback(la, ka)
  mn, nb = pullback_complement(mk, kb)
  mo, oc = pullback_complement(ml, lc)
  od, nd = pushout(mo, mn)
  return Dict(:ml=>ml, :mk=>mk, :mn=>mn, :mo=>mo, :nb=>nb, :oc=>oc, 
              :nd=>nd, :od=>od)
end


end # module 
