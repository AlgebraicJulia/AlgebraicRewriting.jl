"""
Multi-connected-component incremental hom-sets
"""
module IncrementalSum 

using ..IncrementalHom: IncStatic, IncRuntime, IncHomSet, static, runtime, key_dict, pattern
import ..IncrementalHom: validate, additions, state, deletion!, addition!, matches

using ..Constraints: IncConstraints
using ..IncrementalCC: IncCCHomSet, IncCCStatic, IncCCRuntime, key_vect

using Catlab
using Catlab.CategoricalAlgebra.CSets: ACSetColimit
import Catlab: universal

using StructEquality

const × = Iterators.product

"""
`iso` is an isomorphism: apex(coprod) ≅ pattern
"""
@struct_hash_equal struct IncSumStatic <: IncStatic
  pattern::ACSet
  coprod::ACSetColimit
  iso::ACSetTransformation 
  components::Vector{IncCCStatic}
end 

Base.first(h::IncSumStatic) = first(h.components)

additions(h::IncSumStatic) = additions(first(h))

@struct_hash_equal struct IncSumRuntime <: IncRuntime
  key_vect::Vector{Vector{Pair{Int,Int}}}
  key_dict::Dict{Vector{Pair{Int,Int}}, Int}
  components::Vector{IncCCRuntime}
end 

Base.haskey(h::IncSumRuntime, ks::Vector{Pair{Int,Int}}) = all(zip(ks, h.components)) do (k, ihs)
  haskey(ihs, k)
end

Base.first(h::IncSumRuntime) = first(h.components)

state(h::IncSumRuntime) = state(first(h))

"""An incremental Hom Set for a pattern made of distinct connected components"""
@struct_hash_equal struct IncSumHomSet <: IncHomSet
  static::IncSumStatic
  runtime::IncSumRuntime
  constraints::IncConstraints
end

"""
How many additions we've seen so far (including the initialization of the hom 
set). Could be confused with `length(h.components)` or `length(keys(h))`
"""
Base.length(h::IncSumHomSet) = length(first(h))

Base.getindex(h::IncSumHomSet, idx::Int) = h[key_vect(h)[idx]]

Base.getindex(h::IncSumHomSet, idxs::Vector{Pair{Int,Int}}) =
  universal(static(h), [hset[idx] for (hset, idx) in zip(runtime(h).components, idxs)])

Base.haskey(h::IncSumHomSet, ks::Vector{Pair{Int,Int}}) = haskey(runtime(h), ks)


"""Universal property of coprod: induce map from pattern, given component maps"""
matches(h::IncSumHomSet) = 
  universal.(Ref(static(h)), collect.(×(matches.(runtime(h).components)...)))

"""Apply universal property and the isomorphism"""
universal(h::IncSumStatic, comps::Vector{<:ACSetTransformation}) = 
  h.iso ⋅ universal(h.coprod, Multicospan(collect(comps)))

# Extending mutation methods to sums of connected components 
#-----------------------------------------------------------
"""
Delete keys from a component of a IncSumHomSet. This implicitly deletes all 
composite keys that make reference to those keys. 

Returns the *composite keys* which are deleted as an explicit list.
"""
function delete_keys!(runt::IncSumRuntime, component::Int, comp_keys::Vector{Pair{Int,Int}})
  invalidated_keys = []
  comp_keys = Set(comp_keys)
  for composite_key in keys(runt)
    if composite_key[component] ∈ comp_keys 
      push!(invalidated_keys, composite_key) 
      delete!(runt, composite_key)
    end
  end
  return invalidated_keys
end

"""
Add keys to a component of a IncSumHomSet. This implicitly adds composite keys 
for every combination of existing keys in the other components' hom sets.

Returns the *composite keys* which are added as an explicit list.
"""
function add_keys!(runt::IncSumRuntime, component::Int, comp_keys::Vector{Pair{Int,Int}})
  add_keys = []
  ms = [i == component ? comp_keys : keys(ihs) 
        for (i, ihs) in enumerate(runt.components)]
  for newkey in collect.(×(ms...))
    push!(key_vect(runt), newkey)
    push!(add_keys, newkey)
    key_dict(runt)[newkey] = length(key_vect(runt))
  end
  return add_keys
end

"""Propagate deletion/addition for a component to the composite key level""" 
function delete_add_keys!(runt::IncSumRuntime, comp::Int, 
                          inv_keys::Vector{Pair{Int,Int}}, 
                          add_keys::Vector{Pair{Int,Int}})
  return (delete_keys!(runt, comp, inv_keys), add_keys!(runt, comp, add_keys))
end

"""Compute deletions component-wise, then aggregate results"""
function deletion!(stat::IncSumStatic, runt::IncSumRuntime, 
                   constr::IncConstraints, f::ACSetTransformation) 
  deldata = deletion!.(stat.components, runt.components, Ref(constr), Ref(f))
  resdata = [delete_add_keys!(runt, i, inv, add) for (i, (inv, add)) in enumerate(deldata)]
  return (vcat(first.(resdata)...), vcat(last.(resdata)...))
end

"""Compute additions component-wise, then aggregate results"""
function addition!(stat::IncSumStatic, runt::IncSumRuntime, 
                   constr::IncConstraints, i::Int, rmap::ACSetTransformation, 
                   pr::ACSetTransformation)
  adddata = addition!.(stat.components, runt.components, 
                       Ref(constr), i, Ref(rmap), Ref(pr))
  resdata = [delete_add_keys!(runt, i, inv, add) for (i, (inv, add)) in enumerate(adddata)]
  return (vcat(first.(resdata)...), vcat(last.(resdata)...))
end


# Validation
############

"""
Check, with brute computational effort, that the IncrementalHomSet is well 
formed.
"""
function validate(hset::IncSumHomSet)
  (stat, runt, constr) = hset
  allequal(additions.(stat.components)) || error("Addns don't agree")
  allequal(state.(runt.components)) || error("States don't agree")
  allequal(length.(runt.components)) || error("Lengths don't agree")
  codom(stat.iso) == apex(stat.coprod) || error("Bad iso codomain")
  dom(stat.iso) == pattern(hset) || error("Bad iso domain")
  is_epic(stat.iso) && is_monic(stat.iso) || error("Iso not an iso")
  length(stat.components) == length(stat.coprod) || error("len(IHS) != len(CCS)")
  for (i, (h, hs)) in enumerate(zip(stat.coprod, stat.components))
    dom(h) == pattern(hs) || error("Sub-IncHomSet $i mismatch pattern")
  end
  ihs = IncCCHomSet.(stat.components, runt.components, Ref(constr))
  all(validate, ihs) || error("Unnatural component IncrementalHomSet")
end

end # module
