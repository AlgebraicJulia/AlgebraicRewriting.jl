module SqPO 

import ..RewriteUtils: rewrite_match_maps

using ..RewriteDataStructures
using Catlab, Catlab.CategoricalAlgebra



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
function final_pullback_complement(fm::ComposablePair;
    pres::Union{Nothing, Presentation}=nothing, check=false)::ComposablePair
  f, m = fm
  A, B = dom(f), codom(f)
  m_bar = partial_map_classifier_universal_property(m, id(B); pres=pres)
  T_f = partial_map_functor_hom(f; pres=pres)
  pb_2 = pullback(T_f, m_bar)
  _, g = pb_2.cone
  s = Span(partial_map_classifier_eta(A; pres=pres), compose(f,m))
  n = universal(pb_2, s)
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
function rewrite_match_maps(r::Rule{:SqPO},m; pres::Union{Nothing, Presentation}=nothing)
  k, i = final_pullback_complement(ComposablePair(r.L, m); pres=pres)
  r, o = pushout(r.R, k)
  return Dict(:r => r, :o=>o, :k=>k, :i=>i)
end



end # module 
