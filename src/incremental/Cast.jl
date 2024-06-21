"""Cast between IncCC and IncSum"""
module Cast

using ...Rewrite: Rule

using ..IncrementalCC: IncCCStatic, IncCCRuntime, key_vect
import ..IncrementalCC: IncCCHomSet
using ..IncrementalSum: IncSumStatic, IncSumRuntime
import ..IncrementalSum: IncSumHomSet
using ..IncrementalHom: pattern, key_dict, static, runtime, constraints, additions, state
import ..IncrementalHom: IncHomSet
using ..IncrementalConstraints: AC, PAC, NAC, IncConstraints
using ..Algorithms: connected_acset_components, is_combinatorially_monic

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
  stat = IncCCStatic(pattern(hs), constraints(hs), additions(hs))
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
  constr = IncConstraints(monic, pac, nac)
  for add in additions  # TODO: support merging
    is_combinatorially_monic(add) || error("Nonmonic addition $add") 
  end
  coprod, iso = connected_acset_components(pattern)
  single = single || !isempty(constr)
  if single || length(coprod) == 1
    stat = IncCCStatic(pattern, constr, additions)
    runt = IncCCRuntime(pattern, state, constr)
    return IncCCHomSet(stat, runt, constr)
  else 
    pats = dom.(coprod.cocone)
    ccs = IncCCHomSet.(IncCCStatic.(pats, Ref(constr), Ref(additions)), 
                       IncCCRuntime.(pats, Ref(state), Ref(constr)), 
                       Ref(constr))
    stat = IncSumStatic(pattern, coprod, iso, static.(ccs))
    key_vect = sort(vec(collect.(collect(×(keys.(ccs)...)))))
    key_dict = Dict(v => k for (k, v) in enumerate(key_vect))
    runt = IncSumRuntime(key_vect, key_dict, runtime.(ccs))
    return IncSumHomSet(stat, runt, constr)
  end
end

"""
Initialize an Incremental hom set from a rule, using it's pattern `L` as the 
domain of the hom set. Any additions other than the map `I->R` can be passed in
by `additions`, and the schema Presentation can be passed as `S`.
"""
function IncHomSet(rule::Rule{T}, state::ACSet, additions=ACSetTransformation[]
                  ) where T
  pac, nac = [], []
  dpo = (T == :DPO) ? [left(rule)] : ACSetTransformation[]
  right(rule) ∈ additions || push!(additions, right(rule))
  for c in AC.(rule.conditions, Ref(additions), Ref(dpo))
    c isa PAC && push!(pac, c)
    c isa NAC && push!(nac, c)
  end
  IncHomSet(codom(left(rule)), additions, state; monic=rule.monic, pac, nac)
end


end # module