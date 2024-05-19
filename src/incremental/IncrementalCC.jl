"""
An implementation for incremental hom sets where the pattern is a single 
connectect component (or otherwise has constraints that prevent the pattern 
from being broken up)
"""
module IncrementalCC 

using ..Constraints: NAC, IncConstraints, can_match
using ..IncrementalHom: IncStatic, IncRuntime, IncHomSet, pattern, runtime, 
                        key_vect, key_dict
import ..IncrementalHom: validate, additions, state, deletion!, addition!, 
                         matches
using ..Algorithms: compute_overlaps, pull_back, nac_overlap

using Catlab
using Catlab.CategoricalAlgebra.Chase: extend_morphism_constraints  

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

`match_vect`: ground source of truth. It stores, for each update to `state`, 
              what *new* matches were found at that time (+ still exist in the 
              present state - hence the data must be a Dict{Int} rather than a 
              vector, so that we can delete elements). 

`key_vect`: way of indexing this list of dicts where the first element refers 
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
  function IncCCRuntime(pattern::ACSet, initial_state::ACSet, 
                        constr::IncConstraints)
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
    pushed_forward = Dict()
    for (key, match) in pairs(runt.match_vect[idx])
      match′ = match ⋅ update
      # Check whether any NAC / dangling conditions are violated before adding
      if can_match(constr, match′; pac=false) 
        pushed_forward[key] = match′
      else
        delete!(runt, idx => key)
        push!(invalidated_keys, idx => key)
      end
    end
    runt.match_vect[idx] = pushed_forward                       
  end

  # Find newly-introduced matches
  Ob = ob(acset_schema(pattern(stat)))
  X, L = codom(rmap), pattern(stat)
  new_matches, new_keys = Dict{Int, ACSetTransformation}(), Pair{Int, Int}[]

  push!(runt.match_vect, new_matches)
  old_stuff = Dict(o => setdiff(parts(X,o), collect(rmap[o])) for o in Ob)
  seen_constraints = Set() # non-monic match can identify different subobjects 
  for (idx, (subL, mapR)) in enumerate(stat.overlaps[i])
    initial = Dict(map(Ob) do o  # initialize based on overlap btw L and R
      o => Dict(map(parts(dom(subL), o)) do idx
        subL[o](idx) => rmap[o](mapR[o](idx))  # make square commute
      end)
    end)
    initial ∈ seen_constraints && continue
    push!(seen_constraints, initial)
    L_image = Dict(o => Set(collect(subL[o])) for o in Ob)
    boundary = Dict(k => setdiff(parts(L, k), L_image[k]) for k in Ob)
    predicates = Dict(map(Ob) do o
      o => Dict(pₒ => old_stuff[o] for pₒ in boundary[o])
    end)
    for h in homomorphisms(L, X; monic=constr.monic, initial, predicates)
      if h ∈ values(new_matches) # this could be skipped once code is trusted
        error("Duplicating work $h")
      else # PAC?
        @debug "NEW from $subL\n$mapR"
        add_match!(runt, constr, new_keys, new_matches, h)
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
simply have an arbitrary deletion, this is harder. 

A NAC has been deactivated if there exists a morphism N ⇾ X that sends 
all of L to the nondeleted part of X & *some* of N to the deleted portion. The 
deleted portion should be *tiny* compared to the not deleted portion, so it's 
pretty bad to search for all morphisms N->X and filter by those which have 
something which has something in the deleted portion. This means we ought to 
compute the overlaps on the fly in the non-DPO case. 

The `dpo` flag signals that `f` was produced via pushout complement, such that 
any NAC can take advantage of its cached overlaps if it has them. If it is not 
nothing, it contains the morphism `L ↢ I` that was used in POC.

Returns the 'keys' of the deleted matches and added matches.
"""
function deletion!(::IncCCStatic, runt::IncCCRuntime, constr::IncConstraints,  
                   f::ACSetTransformation; dpo=nothing)
  X = codom(f)
  # Initialize variables
  invalidated_keys, new_keys = Pair{Int,Int}[], Pair{Int,Int}[]
  new_matches = Dict{Int, ACSetTransformation}()
  push!(runt.match_vect, new_matches)

  # Check special short circuit case when f is identity
  if force(f) == force(id(X))
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

  # Discover new matches
  non_del_X = Dict(o=>Set(collect(f[o])) for o in ob(acset_schema(X)))
  for nac in constr.nac
    if isnothing(dpo) || !haskey(nac, dpo[1])
      new_nac_homs!(runt, constr, nac, f,  new_keys, new_matches, non_del_X)
    else 
      new_nac_dpo!(runt, constr, nac, f, dpo, new_keys, new_matches, non_del_X)
    end
  end
  # Update state 
  runt.state = dom(f)

  return (invalidated_keys, new_keys)
end

"""
General method for discovering the newly added homs that arise from deleting 
some part of the world due to a NAC.
"""
function new_nac_homs!(runt::IncCCRuntime, constr::IncConstraints, nac::NAC, 
                       f::ACSetTransformation, new_keys, new_matches,
                       X_nondeleted::Dict{Symbol, Set{Int}})
  N, X = codom(nac), codom(f)
  Ob = ob(acset_schema(N))
  for spn in nac_overlap(nac, f) # N ↢ overlap -> X ↢ X'
    overlap = apex(spn)
    overlap_N = Dict(o=>Set(collect(left(spn)[o])) for o in Ob)
    # everything that is not in overlap is forced to go to a non-deleted thing
    predicates = Dict(map(Ob) do o 
      o => Dict([p => X_nondeleted[o] for p in parts(N, o) 
                 if p ∉ overlap_N[o]])
    end)
    # force the triangle to commute
    initial = Dict(map(Ob) do o 
      o=>Dict(map(parts(overlap, o)) do p
        left(spn)[o](p) => right(spn)[o](p)
      end)
    end)
    # get *new* matches that were blocked from existing by this NAC
    for h in homomorphisms(N, X; monic=nac.monic, predicates, initial)
      h′ = pull_back(f, nac.m ⋅ h) # constrained search so that this must work
      add_match!(runt, constr, new_keys, new_matches, h′)
    end
  end
end

"""
Given dpo, a composable pair I→L→X, we use the latter morphism as a key into
the NAC to access a complete set of overlaps L ↢ O → N that send *some* part 
of N/L to some part of L/I.
"""
function new_nac_dpo!(runt::IncCCRuntime, constr::IncConstraints, nac::NAC, 
                      f::ACSetTransformation, dpo, new_keys, new_matches,
                      X_nondeleted::Dict{Symbol, Set{Int}})
  N, X, (l, match) = codom(nac), codom(f), dpo
  overlaps, Ob, seen = nac[l], ob(acset_schema(N)), Set{Dict}() 
               
  for (to_L, to_N) in overlaps
    # make O->L->X commute with O->N->X
    initial = extend_morphism_constraints(to_L ⋅ match, to_N)
    
    # some overlaps are identified with each other due to non-monic match. 
    (isnothing(initial) || initial ∈ seen) && continue 
    push!(seen, initial)

    # Everything not in the image of the overlap must go to non-deleted X
    overlap_N = Dict(o => Set(collect(to_N[o])) for o in Ob) # store to_N image
    predicates = Dict(map(Ob) do o
      o => Dict(p => X_nondeleted[o] for p in parts(N, o) if p ∉ overlap_N[o])
    end)

    # get *new* matches that were blocked from existing by this NAC
    for h in homomorphisms(N, X; predicates, initial)
      h′ = pull_back(f, nac.m ⋅ h) # constrained search so that this must work
      add_match!(runt, constr, new_keys, new_matches, h′)
    end
  end
end

"""Add a match during a deletion"""
function add_match!(runt::IncCCRuntime, constr::IncConstraints,      
                    new_keys, new_matches, m::ACSetTransformation)
  if can_match(constr, m)
    new_key = length(runt) => length(new_keys)+1
    push!(key_vect(runt), new_key)
    push!(new_keys, new_key)
    key_dict(runt)[new_key] = length(key_vect(runt))
    new_matches[length(new_keys)] = m 
  end
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
