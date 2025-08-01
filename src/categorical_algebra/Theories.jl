module Theories 

export ThPushoutComplement, pushout_complement, can_pushout_complement, pushout_complement_violations

using GATlab
using Catlab: ComposablePair, ThCategory, TrivialCat

# @theory ThCategoryWithPairs <: ThCategory begin 
#   CmpPair(a::Ob,c::Ob)::TYPE
#   elbow(p::CmpPair(a,c))::Ob ⊣ [(a,c)::Ob]
#   mk_pair(f::(a→b),g::(b→c))::CmpPair(a,c) ⊣ [(a,b,c)::Ob]
#   fst(p::CmpPair(a,c))::CmpPair(a,elbow(p)) ⊣ [(a,c)::Ob]
#   snd(p::CmpPair(a,c))::CmpPair(elbow(p),c) ⊣ [(a,c)::Ob]
# end

""" Pushout complement: extend composable pair to a pushout square.

[Pushout complements](https://ncatlab.org/nlab/show/pushout+complement) are the
essential ingredient for double pushout (DPO) rewriting.

`pushout_complement` only expected to not error if 
`pushout_complement_violations` returns empty list
"""
@theory ThPushoutComplement <: ThCategory begin
  Pair::TYPE{ComposablePair}
  Vec′::TYPE{Vector}
  pushout_complement_violations(p::Pair)::Vec′
  pushout_complement(p::Pair)::Pair 
end 

@model_method can_pushout_complement

can_pushout_complement(m::WithModel, p::ComposablePair; context=nothing) = 
  isempty(pushout_complement_violations(m, p; context))

can_pushout_complement(m::WithModel, f, g;  context=nothing) = 
  can_pushout_complement(m, ComposablePair(f,g; cat=getvalue(m)); context) 
 
pushout_complement(m::WithModel, f, g; context=nothing) = 
  pushout_complement(m, ComposablePair(f,g; cat=getvalue(m)); context) 

@instance ThPushoutComplement{Nothing, Nothing} [model::TrivialCat] begin 
  pushout_complement_violations(::ComposablePair) = []
  pushout_complement(::ComposablePair) = ComposablePair(nothing, nothing; cat=model)
end

end # module
