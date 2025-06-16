module SqPO 

using Catlab, Catlab.CategoricalAlgebra

using ...CategoricalAlgebra.PartialMap
using ..Utils
import ..Utils: rewrite_match_maps


# Sesqui-pushout rewriting
##########################

"""
The specification for the following functions comes from:
  - 'Concurrency Theorems for Non-linear Rewriting Theories'
     - for final pullback complement and sesqui-pushout rewriting
  - 'AGREE - Algebraic Graph Rewriting with Controlled Embedding'
     - for partial map classifier (a functor T and natural transformation η)

This implementation is specialized to rewriting CSets
"""

"""
See Theorem 2 of 'Concurrency Theorems for Non-linear Rewriting Theories'
      f
  B <--- A
m ↓      ↓ n
  C <--  D
     g

"""
function final_pullback_complement(fm::ComposablePair; cat,
    pres::Union{Nothing, Presentation}=nothing, check=false)::ComposablePair
  f, m = fm
  A, B = dom[cat](f), codom[cat](f)
  m_bar = partial_map_classifier_universal_property(m, id[cat](B); cat, pres=pres)
  T_f = partial_map_functor_hom(f; pres=pres)
  pb_2 = pullback[cat](T_f, m_bar)
  _, g = pb_2.cone
  s = Span(partial_map_classifier_eta(A; cat, pres=pres), compose[cat](f,m))
  n = universal[cat](pb_2, s)
  !check || is_isomorphic(apex(pullback(m,g)), A) || error("incorrect")
  return ComposablePair(n, g)
end

"""    rewrite_match_maps(r::Rule{:SqPO},m; pres::Union{Nothing, Presentation}=nothing)
Sesqui-pushout is just like DPO, except we use a final pullback complement
instead of a pushout complement.

    r.L  r.R
  L <-⌞K -> R
m ↓    ↓k   ↓ r
  I <- • ->⌜O
     i   o
"""
function rewrite_match_maps(r::Rule{:SqPO},m; cat, pres::Union{Nothing, Presentation}=nothing)
  k, i = final_pullback_complement(ComposablePair(r.L, m); cat, pres=pres)
  r, o = pushout[cat](r.R, k)
  return Dict(:r => r, :o=>o, :k=>k, :i=>i)
end

end # module 
