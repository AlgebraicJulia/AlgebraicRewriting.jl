"""
Things for incremental hom sets, not particular to any specific implementation.
"""
module IncrementalHom

export IncHomSet, matches, validate, addition!, deletion!

using Catlab

using ...Rewrite: Rule, rewrite_match_maps, get_match
using ...Rewrite.Utils: get_result, get_rmap, get_pmap, get_expr_binding_map
import ...Rewrite: rewrite!
using ..IncrementalConstraints: compat_constraints

"""
There are currently two types of IncHomSets. Common to both is a separation of 
the data required to specify which hom-set is being maintained (`static`) and 
the data structure required to be maintained as some target `X` is changing 
(`runtime`). We also distinguish between general static data for maintaining 
an incremental hom-set from further static data about various constraints on 
that process (`constraints`). 

These are all currently designed to work with `DenseParts` ACSets but could be 
straightforwardly modified to work with `MarkAsDeleted` ACSets (which would be 
even more efficient.)
"""
abstract type IncHomSet end

function validate end # extended by IncCCHom and IncSumHom
function matches end


static(h::IncHomSet)::IncStatic = h.static

runtime(h::IncHomSet)::IncRuntime = h.runtime

constraints(h::IncHomSet) = h.constraints

additions(h::IncHomSet) = additions(static(h))

pattern(h::IncHomSet) = pattern(static(h))

Base.keys(h::IncHomSet) = keys(key_dict(h))

state(h::IncHomSet) = state(runtime(h))

key_vect(h::IncHomSet) = key_vect(runtime(h))

key_dict(h::IncHomSet) = key_dict(runtime(h))

Base.delete!(i::IncHomSet, k) = delete!(runtime(i), k)

Base.iterate(hs::IncHomSet) = 
  iterate([static(hs), runtime(hs), constraints(hs)])

Base.iterate(hs::IncHomSet, i) = 
  iterate([static(hs), runtime(hs), constraints(hs)], i)


"""
A incremental hom-set has a fixed pattern, `pattern` (sometimes referred to by 
a variable, `L`). It is updated with respect to a class of changes to `state` 
(sometimes referred to by a variable `X`).

The state, X, can be changed via restriction to subobjects or by pushout with 
any of the predeclared monic `addition` morphisms, though we won't know the 
match morphism •→X until runtime.

                              additionⱼ
                            I >--------> R
                            ↓          ⌜ ↓
                            X ---------> X′

Cached `overlaps` data helps compute how the hom set updates with respect to a 
given addition being applied. The cache records in element i data for when we 
are updating the hom set after having applied addition i. It stores 
partial overlaps between L and Rᵢ which have *some* data that hits upon the 
new content added.
"""
abstract type IncStatic end

pattern(h::IncStatic) = h.pattern


"""
Runtimes must have a `state`, `key_vect`, and `key_dict`.

`state`: The current state of the world, into which we are maintaining a 
         hom-set. 

`key_vect::Vector{K}`: A vector of keys into the ground source of truth, which 
                       stores the data of the morphisms. The structure of this 
                       source of truth and key type K depends on which kind of 
                       `IncRuntime` is being used. This may contain references 
                       to invalidated homs.

`key_dict::Dict{K, Int}`: Contains an entry for each current element of the 
                          hom-set. The values are used to index `key_vect`.
"""
abstract type IncRuntime end

Base.keys(h::IncRuntime) = keys(key_dict(h))

key_vect(h::IncRuntime) = h.key_vect

key_dict(h::IncRuntime) = h.key_dict 

Base.getindex(i::IncRuntime, idx::Int)::ACSetTransformation = i[key_vect(i)[idx]]

Base.delete!(i::IncRuntime, k) = delete!(key_dict(i), k)

Base.pairs(h::IncHomSet) = [k => h[k] for k in keys(key_dict(h))]

# Addition
##########

"""Perform a pushout addition given a match morphism from the domain."""
addition!(hset::IncHomSet, i::Int, omap::ACSetTransformation) =
  addition!(hset, i, pushout(additions(hset)[i], omap)...)


# Unpacking into components
###########################

addition!(hset::IncHomSet, i::Int, rmap::ACSetTransformation, 
          update::ACSetTransformation) = addition!(hset..., i , rmap, update)

deletion!(hset::IncHomSet, f::ACSetTransformation; kw...) = 
  deletion!(hset..., f; kw...)


# Rewriting: combined deletion! then addition!
##############################################

"""Perform a rewrite! with an arbitrary match"""
function rewrite!(hset::IncHomSet, r::Rule) 
  m = get_match(r, state(hset))
  isnothing(m) ? nothing : rewrite!(hset, r, m)
end

"""
Use a rewrite rule to induce a deletion followed by an addition.

Returns the keys of deleted and added matches, respectively.
"""
function rewrite!(hset::IncHomSet, r::Rule{T}, match::ACSetTransformation; 
                 check_compat=false) where T
  # Check input data
  if check_compat 
    c_err = compat_constraints(constraints(hset), r) 
    isnothing(c_err) || error("Constraint mismatch: $c_err")
  end
  i = findfirst(==(right(r)), additions(hset)) # RHS of rule must be an addition
  state(hset) == codom(match)|| error("Codom mismatch for match $match")
  dpo = T == :DPO ? (left(r), match) : nothing

  # Perform rewrite, unpack results
  rw_result = rewrite_match_maps(r, match)
  del_map, pushforward_no_attr = get_pmap(T, rw_result)
  pushforward_attr = get_expr_binding_map(r, match, rw_result)
  pushforward = pushforward_no_attr ⋅ pushforward_attr
  rmap = get_rmap(T, rw_result) ⋅ pushforward_attr

  # Use results to update hom set
  del_invalidated, del_new = deletion!(hset, del_map; dpo)
  add_invalidated, add_new = addition!(hset, i, rmap, pushforward)
  (vcat(del_invalidated, add_invalidated), vcat(del_new, add_new))
end

end # module