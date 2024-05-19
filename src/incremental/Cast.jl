"""Cast between IncCC and IncSum"""
module Cast

using ...Rewrite: Rule

using ..IncrementalCC: IncCCStatic, IncCCRuntime, key_vect
import ..IncrementalCC: IncCCHomSet
using ..IncrementalSum: IncSumStatic, IncSumRuntime
import ..IncrementalSum: IncSumHomSet
using ..IncrementalHom: pattern, key_dict, static, runtime, constraints, additions, state
import ..IncrementalHom: IncHomSet
using ..Constraints: AC, PAC, NAC, IncConstraints
using ..Algorithms: connected_acset_components

using Catlab 

const × = Iterators.product

# No-ops
########

IncCCHomSet(hs::IncCCHomSet) = hs

IncSumHomSet(hs::IncSumHomSet) = hs

# Casting
#########

"""Cast a sum homset into a single 'connected component'"""
function IncCCHomSet(hs::IncSumHomSet)
  stat = IncCCStatic(pattern(hs), additions(hs))
  runt = IncCCRuntime(pattern(hs), state(hs), constraints(hs))
  IncCCHomSet(stat, runt, constraints(hs))
end

"""Cast a CC to a singleton sum"""
function IncSumHomSet(hs::IncCCHomSet) 
  pat = pattern(hs)
  kv = [[x] for x in key_vect(hs)]
  kd = Dict([k] => v for (k,v) in key_dict(hs))
  stat = IncSumStatic(pat, coproduct([pat]), id(pat), [static(hs)])
  runt = IncSumRuntime(kv, kd, [runtime(hs)])
  IncSumHomSet(stat, runt, constraints(hs))
end

# User-facing constructor
#########################

"""
Automatically determine whether one creates an IncCC or an IncHom.

`single` keyword forces the pattern to be treated as a single CC, even if it's 
not one. Having any constraints will also force it to be treated as a single CC.
"""
function IncHomSet(pattern::ACSet, additions::Vector{<:ACSetTransformation}, 
                   state::ACSet; single=false, monic=false, pac=[], nac=[])
  obs = ob(acset_schema(pattern))
  monic = monic isa Bool ? (monic ? obs : []) : monic
  pac, nac = PAC.(pac), NAC.(nac)
  constraints = IncConstraints(monic, pac, nac)
  all(is_monic, additions) || error("Nonmonic addition") # TODO: support merging
  coprod, iso = connected_acset_components(pattern)
  single = single || !isempty(constraints)
  if single || length(coprod) == 1
    stat = IncCCStatic(pattern, additions)
    runt = IncCCRuntime(pattern, state, constraints)
    return IncCCHomSet(stat, runt, constraints)
  else 
    pats = dom.(coprod.cocone)
    ccs = IncCCHomSet.(IncCCStatic.(pats, Ref(additions)), 
                       IncCCRuntime.(pats, Ref(state), Ref(constraints)), 
                       Ref(constraints))
    stat = IncSumStatic(pattern, coprod, iso, static.(ccs))
    key_vect = sort(vec(collect.(collect(×(keys.(ccs)...)))))
    key_dict = Dict(v => k for (k, v) in enumerate(key_vect))
    runt = IncSumRuntime(key_vect, key_dict, runtime.(ccs))
    return IncSumHomSet(stat, runt, constraints)
  end
end

function IncHomSet(rule::Rule{T}, state::ACSet) where T
  pac, nac = [], []
  dpo = (T == :DPO) ? [left(rule)] : []
  for c in AC.(rule.conditions, Ref(dpo))
    c isa PAC && push!(pac, c)
    c isa NAC && push!(nac, c)
  end
  IncHomSet(codom(left(rule)), [right(rule)], state; monic=rule.monic, pac, nac)
end


end # module