"""
An implementation for incremental hom sets where the pattern is a single 
connectect component (or otherwise has constraints that prevent the pattern 
from being broken up)
"""
module IncrementalCC 

using ..Constraints: IncConstraints, can_match
using ..IncrementalHom: IncStatic, IncRuntime, IncHomSet, pattern, runtime, 
                        key_vect, key_dict
import ..IncrementalHom: validate, additions, state, deletion!, addition!, matches
using ..Algorithms: compute_overlaps, pull_back

using Catlab

using StructEquality

"""
For `IncCCHomSet` the pattern `L` must be a single connected component.
"""
@struct_hash_equal struct IncCCStatic <: IncStatic
  pattern::ACSet
  additions::Vector{ACSetTransformation}
  overlaps::Vector{Vector{Span}}
  function IncCCStatic(pattern::ACSet, adds=[])
    hs = new(pattern, [], [])
    push!.(Ref(hs), adds)
    return hs 
  end
end

additions(h::IncCCStatic) = h.additions

"""Consider a new addition (and compute its partial overlaps w/ the pattern)"""
function Base.push!(hs::IncCCStatic, addition::ACSetTransformation)
  push!(hs.additions, addition)
  push!(hs.overlaps, compute_overlaps(pattern(hs), addition))
end

"""
This assumes the state of the world is changed in discrete updates.

`match_vect`: the ground source of truth. It stores, for each update to `state`, 
              what *new* matches were found at that time (and still exist in the 
              present state - hence the data must be a Dict{Int} rather than a 
              vector, so that we can delete elements). 

`key_vect`: a way of indexing this list of dicts where the first element refers 
            to an index of `match_vect` and the second element refers to the 
            keys in the associated Dict. This gives us a single-integer value 
            way of referring to *every* hom that has been seen, including the 
            deleted ones. Thus the current # of matches is *not* 
            `length(key_vect)`.

`key_dict`: the relationship between `match_vect` and `key_vect`. There is an 
            one element in the dictionary for every key (across all the 
            dictionaries in `match_vect`). The keys of this dictionary are 
            keys of `match_vect`, and the values are the keys of `key_vect`.
            So the current # of matches *is* length(key_dict), modulo any 
            post-hoc constraints.
"""
@struct_hash_equal mutable struct IncCCRuntime <: IncRuntime
  const match_vect::Vector{Dict{Int, ACSetTransformation}}
  const key_vect::Vector{Pair{Int,Int}}
  const key_dict::Dict{Pair{Int,Int}, Int}
  state::ACSet
  function IncCCRuntime(pattern::ACSet, initial_state::ACSet, constr::IncConstraints)
    homs = filter(h -> can_match(constr, h), 
                  homomorphisms(pattern, initial_state; monic=constr.monic))
    n = length(homs)
    match_vect = [Dict(enumerate(homs))]
    key_vect = Pair{Int,Int}[1 => i for i in 1:n]
    key_dict = Dict{Pair{Int,Int},Int}((1 => i) => i for i in 1:n)
    return new(match_vect, key_vect, key_dict, initial_state)
  end
end

state(h::IncCCRuntime) = h.state


"""Package static and runtime data together"""
@struct_hash_equal struct IncCCHomSet <: IncHomSet
  static::IncCCStatic
  runtime::IncCCRuntime
  constraints::IncConstraints
end

Base.getindex(i::IncCCHomSet, idx::Int)::ACSetTransformation = runtime(i)[idx]

"""
How many additions we've seen so far (including the initialization of the hom 
set). This could be confused with giving the total number of matches, which is 
instead `length(keys(hset))`
"""
Base.length(i::IncCCHomSet) = length(match_vect(i))
Base.length(i::IncCCRuntime) = length(match_vect(i))

Base.haskey(h::IncCCHomSet, k::Pair{Int,Int}) = haskey(runtime(h), k)
Base.haskey(h::IncCCRuntime, k::Pair{Int,Int}) = haskey(key_dict(h), k)
Base.getindex(i::IncCCHomSet, ij::Pair{Int,Int}) = runtime(i)[ij]
Base.getindex(i::IncCCRuntime, ij::Pair{Int,Int}) = match_vect(i)[ij[1]][ij[2]]

match_vect(h::IncCCHomSet) = match_vect(runtime(h))
match_vect(h::IncCCRuntime) = h.match_vect

matches(h::IncCCHomSet) = matches(runtime(h))
matches(h::IncCCRuntime) = [h[k] for k in keys(h)]


"""
Add to `matches` based on an addition #i specified via a pushout (rmap, update)

                 For all overlaps:  apex ↪ L
                                    ↓      ⇣ (find all of these!) 
 Hom(L, X_old) => Hom(L, X)         Rᵢ ⟶  X
                                    rmap ⌞ ↑ update
                                          X_old

However, we only want maps L → X where elements not in the image of L are all 
sent to X elements which outside of the image of rmap.

This is to avoid double-counting with a slightly bigger overlap which has 
already been calculated between L and Rᵢ.

Note, adding things can also invalidate old matches if there are negative
application or dangling conditions.

Returns the 'keys' of the deleted matches and added matches.
"""
function addition!(stat::IncCCStatic, runt::IncCCRuntime, constr::IncConstraints,
                   i::Int, rmap::ACSetTransformation, update::ACSetTransformation)  
  invalidated_keys = Pair{Int,Int}[]

  # Push forward old matches
  for idx in 1:length(runt)
    dic = Dict()
    for (k, m) in pairs(runt.match_vect[idx])
      m′ = m ⋅ update
      # Check whether any NAC / dangling conditions are violated before adding
      if can_match(constr, m′; pac=false) 
        dic[k] = m′
      else
        delete!(runt, idx => k)
        push!(invalidated_keys, idx => k)
      end
    end
    runt.match_vect[idx] = dic                       
  end

  # Find newly-introduced matches
  S = acset_schema(pattern(stat))
  X, L = codom(rmap), pattern(stat)
  new_matches, new_keys = Dict{Int, ACSetTransformation}(), Pair{Int,Int}[]

  push!(runt.match_vect, new_matches)
  old_stuff = Dict(o => setdiff(parts(X,o), collect(rmap[o])) for o in ob(S))
  seen_constraints = Set() # non-monic match can identify different subobjects 
  for (idx, (subL, mapR)) in enumerate(stat.overlaps[i])
    initial = Dict(map(ob(S)) do o  # initialize based on overlap btw L and R
      o => Dict(map(parts(dom(subL), o)) do idx
        subL[o](idx) => rmap[o](mapR[o](idx))  # make square commute
      end)
    end)
    if initial ∉ seen_constraints
      push!(seen_constraints, initial)
      L_image = Dict(o => Set(collect(subL[o])) for o in ob(S))
      boundary = Dict(k => setdiff(parts(L,k), L_image[k]) for k in ob(S))
      predicates = Dict(o => Dict(pₒ => old_stuff[o] for pₒ in boundary[o]) 
                        for o in ob(S))
      for h in homomorphisms(L, X; monic=constr.monic, initial, predicates)
        if h ∈ values(new_matches) # this could be skipped once code is trusted
          error("Duplicating work $h")
        else # PAC?
          @debug "NEW from $subL\n$mapR"
          new_key = length(runt) => length(new_keys)+1
          push!(key_vect(runt), new_key)
          push!(new_keys, new_key)
          key_dict(runt)[new_key] = length(key_vect(runt))
          new_matches[length(new_keys)] = h 
        end
      end
    end
  end
  runt.state = X
  return (invalidated_keys, new_keys)
end


"""
Delete / modify existing matches based on the target ACSet being permuted or 
reduced to a subobject. If a match touches upon something which is deleted, 
remove the match. Given X ↩ X′ we are updating Hom(L, X) => Hom(L, X′)

In the presence of negative application conditions / dangling condition, 
a deletion can also *add* new matches. When deletion is performed by DPO, we 
can know statically where to search for newly added morphisms. However, if we 
simply have an arbitrary deletion, 

A NAC has been deactivated if there exists a morphism N ⇾ X that sends 
all of L to the nondeleted part of X and *some* of N to the deleted portion.


Returns the 'keys' of the deleted matches and added matches.
"""
function deletion!(::IncCCStatic, runt::IncCCRuntime, constr::IncConstraints,  
                   f::ACSetTransformation)

  # Initialize variables
  invalidated_keys, new_keys = Pair{Int,Int}[], Pair{Int,Int}[]
  new_matches = Dict{Int, ACSetTransformation}()
  push!(runt.match_vect, new_matches)

  # Check special short circuit case
  if force(f) == force(id(dom(f)))
    return (Pair{Int,Int}[], Pair{Int,Int}[]) # nothing happens
  end

  # Update old matches
  for (idx, dic) in enumerate(match_vect(runt))
    for (idx′, m) in collect(dic)
      m′ = pull_back(f, m)
      # Delete if match refers to something deleted OR we have invalidated a PAC
      if isnothing(m′) || !can_match(constr, m′; nac=false)
        delete!(dic, idx′)
        delete!(key_dict(runt), idx => idx′)
        push!(invalidated_keys, idx => idx′)
      else 
        dic[idx′] = m′
      end
    end
  end

  # Update state 
  runt.state = dom(f)

  # Discover new matches
  if !all(is_isomorphic, components(f))
    for n in constr.nac
      for h in homomorphisms(codom(n), state(runt); monic=n.monic)
        if can_match(constr, h; pac=true)
          new_key = length(runt) => length(new_keys)+1
          push!(key_vect(runt), new_key)
          push!(new_keys, new_key)
          key_dict(runt)[new_key] = length(key_vect(runt))
          new_matches[length(new_keys)] = h 
        end
      end
    end
  end
  return (invalidated_keys, new_keys)
end

# Validation 
############
"""
Check, with brute computational effort, that the IncrementalHomSet is well 
formed.
"""
function validate(hset::IncCCHomSet)
  ms = matches(hset)
  all(is_natural, ms) || error("Unnatural")
  all(==(pattern(hset)), dom.(ms)) || error("Bad dom")
  all(==(state(hset)), codom.(ms)) || error("Bad codom")
  ref = IncHomSet(pattern(hset), additions(hset), state(hset))
  xtra = setdiff(ms, values(first(match_vect(ref))))
  missin = setdiff(values(first(match_vect(ref))), ms)
  isempty(xtra ∪ missin) || error("\n\textra $xtra \n\tmissing $missin")
end

end # module
