"""
Incremental homomorphism search
"""
module Incremental 
export IncHomSet, IncHomSets, rewrite!, matches

using ..Rewrite
using ..Rewrite.Utils: get_result, get_rmap, get_pmap, get_expr_binding_map
using ..CategoricalAlgebra.CSets: invert_iso, extend_morphism
import ..Rewrite: rewrite!, can_match

using StructEquality
using Catlab
import Catlab: universal
using Catlab.CategoricalAlgebra.CSets: ACSetColimit
using Catlab.CategoricalAlgebra.HomSearch: total_parts

const × = Iterators.product
# Data Structures 
#################

# Application conditions
#-----------------------
"""
An application condition (w/r/t a pattern, L) is given by a morphism out of L.
This can be given two semantics, based on the existence of a particular 
morphism making a triangle commute. We can furthermore impose monic 
constraints on that derived morphism.
"""
abstract type AC end

"""
Coerce a general `Constraint` into a simple application condition, if possible. 
This works if the `Constraint` was created by `AppCond`.
"""
function AC(c::Constraint)
  m = c.g[1,:elabel]
  monic = c.d.expr.monic
  AppCond(m; monic) == c && return PAC(m, monic)
  AppCond(m, false; monic) == c && return NAC(m, monic)
  return nothing
end

"""
A negative application condition L -> N means a match L -> X is invalid if 
there exists a commuting triangle.  
"""
@struct_hash_equal struct NAC <: AC 
  m::ACSetTransformation
  monic::Vector{Symbol}
end

NAC(n::NAC) = n

NAC(m::ACSetTransformation, b::Bool=false) = 
  NAC(m, b ? ob(acset_schema(dom(m))) : [])

"""
A negative application condition L -> N means a match L -> X is invalid if 
there does not exist a commuting triangle.  
"""
@struct_hash_equal struct PAC <: AC
  m::ACSetTransformation
  monic::Union{Bool, Vector{Symbol}}
end

PAC(p::PAC) = p

PAC(m::ACSetTransformation, b::Bool=false) = 
  PAC(m, b ? ob(acset_schema(dom(m))) : [])

# Abstract types
#---------------

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

static(h::IncHomSet)::IncStatic = h.static

runtime(h::IncHomSet)::IncRuntime = h.runtime

constraints(h::IncHomSet) = h.constraints

additions(h::IncHomSet) = additions(static(h))

pattern(h::IncHomSet) = pattern(static(h))

Base.keys(h::IncHomSet) = keys(key_dict(h))

state(h::IncHomSet) = state(runtime(h))

matches(h::IncHomSet) = matches(runtime(h))

key_vect(h::IncHomSet) = key_vect(runtime(h))

key_dict(h::IncHomSet) = key_dict(runtime(h))

Base.delete!(i::IncHomSet, k) = delete!(runtime(i), k)

set_state!(i::IncHomSet, X::ACSet) = set_state!(runtime(i), X)

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

matches(h::IncRuntime) = [h[k] for k in keys(h)]

key_vect(h::IncRuntime) = h.key_vect

key_dict(h::IncRuntime) = h.key_dict 

Base.getindex(i::IncRuntime, idx::Int)::ACSetTransformation = i[key_vect(i)[idx]]

Base.delete!(i::IncRuntime, k) = delete!(key_dict(i), k)

function set_state!(i::IncRuntime, X::ACSet)  
  i.state = X
end

"""
We may not be merely interested maintaining a set of matches 
Hom(L,X), but instead we care only about the monic morphisms, or morphisms that 
satisfy some positive/negative application conditions (PAC/NAC). In particular, 
NAC poses a new challenge: deletion can introduce new matches. There are various
ways of dealing with this, one of which would require predeclaring `deletion` 
morphisms `L ↢ I`. However, that approach would only work for DPO. So a less 
efficient approach that uses only the data of X ↢ X′ and I→N is to search for 
all morphisms that send *some* part of N to a deleted part of X and all of L to
the nondeleted part of X (this will find all of the new morphisms, only the 
new morphisms, but will possibly contain duplicates).

TODO add `dangling` field
"""
@struct_hash_equal struct IncConstraints 
  monic::Vector{Symbol}
  pac::Vector{PAC}
  nac::Vector{NAC}
end

Base.isempty(c::IncConstraints) = all(isempty, [c.monic,c.pac,c.nac])

"""
Check whether a putative hom meets the constraints. Kwargs control which checks 
are run. Often these homs are generated via hom search using the monic 
constraint, so the monic constraint is usually not checked.
"""
function can_match(constr::IncConstraints, m::ACSetTransformation; 
                   monic::Bool=false, pac=true, nac=true)::Bool

  !monic || all(o -> is_monic(m[o]), constr.monic) || return false

  if pac 
    for ac in constr.pac
      isnothing(extend_morphism(m, ac.m;  monic=ac.monic)) && return false
    end
  end
  
  if nac 
    for ac in constr.nac
      isnothing(extend_morphism(m, ac.m;  monic=ac.monic)) || return false
    end
  end
  
  return true
end

"""
Check if a rule imposes the same constraints as captured by an IncConstraint

TODO handle dangling condition specially (add it as a field to IncConstraints) 
"""
function compat_constraints(constraints::IncConstraints, r::Rule{T}) where T
  # (T == DPO && constraints.dangling == left(r)) || return false
  cm, rm = Set.([constraints.monic, r.monic])
  cm == rm || return "Monic mismatch: $cm != $rm"
  nac, pac = Set(), Set()
  for constr in AC.(r.conditions)
    push!(constr isa PAC ? pac : nac, constr)
  end 
  Set(constraints.nac) == nac || return "NAC mismatch" 
  Set(constraints.pac) == pac || return "PAC mismatch"
  return nothing
end

# Single-connected-component incremental hom sets
#------------------------------------------------

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

IncCCHomSet(hs::IncCCHomSet) = hs

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

# Multi-connected-component incremental hom sets
#-----------------------------------------
@struct_hash_equal struct IncSumStatic <: IncStatic
  pattern::ACSet
  coprod::ACSetColimit
  iso::ACSetTransformation # apex(coprod) ≅ pattern
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

IncSumHomSet(hs::IncSumHomSet) = hs

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

"""
`single` keyword forces the pattern to be treated as a single connected 
component, even if it's not
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

# Algorithms 
############

"""
Break an ACSet into connected components, represented as a coproduct and an 
isomorphism from the original ACSet into the colimit apex.
"""
function connected_acset_components(X::ACSet)
  isempty(X) && return (coproduct([X]), id(X))  # edge case
  S = acset_schema(X)
  g = Graph()
  # Part dict maps X indices to graph vertices, part lookup goes other way
  part_dict, part_lookup = Dict(), Pair{Symbol, Int}[]
  for o in types(S) 
    append!(part_lookup, [o => p for p in parts(X, o)])
    vs = add_vertices!(g, nparts(X, o))
    part_dict[o] = Dict(zip(parts(X, o), vs))
  end
  for (h, s, t) in homs(S)
    for p in parts(X, s)
      add_edge!(g, part_dict[s][p], part_dict[t][X[p, h]])
    end
  end
  for (h, s, t) in attrs(S)
    for p in parts(X, s)
      fp = X[p, h]
      if fp isa AttrVar
        add_edge!(g, part_dict[s][p], part_dict[t][fp.val])
      end
    end
  end

  ιs = map(enumerate(connected_components(g))) do (i, cc)
    d = Dict(o=>Int[] for o in types(S))
    for elem in cc
      (o, idx) = part_lookup[elem]
      push!(d[o], idx)
    end 
    comp = constructor(X)()
    copy_parts!(comp, X; d...)
    ACSetTransformation(comp, X; Dict(k=>k ∈ ob(S) ? v : AttrVar.(v) 
                                      for (k, v) in pairs(d))...)
  end |> Multicospan
  cp = coproduct(dom.(ιs))
  return (cp, invert_iso(universal(cp, ιs)))
end

"""
Find all partial maps from the pattern to the addition, with some restrictions:
1. Something must be mapped into the newly added material.
2. Anything in L incident to a part mapped onto newly added material must be 
   mapped to newly added material
"""
function compute_overlaps(L::ACSet, I_R::ACSetTransformation)::Vector{Span}
  overlaps = Span[]
  for subobj in hom.(subobject_graph(L)[2])
    abs_subobj = abstract_attributes(dom(subobj))
    for h in homomorphisms(dom(abs_subobj), codom(I_R))
      lft = abs_subobj ⋅ subobj
      good_overlap(lft, h, I_R) && push!(overlaps, Span(lft, h))
    end
  end
  return overlaps
end

function good_overlap(subobj::ACSetTransformation, h::ACSetTransformation, 
                      I_R::ACSetTransformation)
  S = acset_schema(dom(h))
  L = codom(subobj)
  # Parts of L which are mapped to newly added material via partial map
  new_mat = Dict(k=>Set{Int}() for k in types(S)) 
  for k in ob(S)
    for i in parts(dom(h), k)
      hᵢ = h[k](i)
      if hᵢ ∉ collect(I_R[k])
        push!(new_mat[k], subobj[k](i))
      end
    end
  end
  for k in attrtypes(S)
    for i in AttrVar.(parts(dom(h), k))
      hᵢ = h[k](i)
      if hᵢ isa AttrVar && subobj[k](i) isa AttrVar && hᵢ.val ∉ collect(I_R[k])
        push!(new_mat[k], subobj[k](i).val)
      end
    end
  end
  all(isempty, values(new_mat)) && return false # fail condition 1
  for k in ob(S)
    for p in setdiff(parts(L, k), collect(subobj[k]))
      for (f, _, cd) in homs(S; from=k)
        cd == k && continue # see comment in docstring about DDS
        L[p, f] ∈ new_mat[cd] && return false # fail condition 2
      end
    end
  end
  return true
end

"""
Add to `matches` based on an addition #i specified via a pushout (rmap, update)

                 For all overlaps:  apex ↪ L
                                    ↓      ⇣ (find all of these!) 
 Hom(L, X_old) => Hom(L, X)         Rᵢ ⟶  X
                                    rmap ⌞ ↑ update
                                          X_old

However, we only want maps L → X where elements not in the image of L are all 
sent to X elements which outside of the image of rmap.

This is to avoid double-counting with a slightly bigger 
overlap which has already been calculated between L and Rᵢ.

Returns the 'keys' of the added matches.
"""
addition!(hset::IncHomSet, i::Int, rmap::ACSetTransformation, 
  update::ACSetTransformation) = addition!(hset..., i , rmap, update)

function addition!(static::IncCCStatic, runtime::IncCCRuntime, constraints::IncConstraints,
                   i::Int, rmap::ACSetTransformation, update::ACSetTransformation)
  S = acset_schema(pattern(static))
  invalidated_keys = Pair{Int,Int}[]
  # Push forward old matches
  for idx in 1:length(runtime)
    dic = Dict()
    for (k, m) in pairs(runtime.match_vect[idx])
      m′ = m ⋅ update
      # Check whether any NAC / dangling conditions are violated before adding
      if can_match(constraints, m′; pac=false) 
        dic[k] = m′
      else
        delete!(runtime, idx => k)
        push!(invalidated_keys, idx => k)
      end
    end
    runtime.match_vect[idx] = dic                       
  end

  # Find newly-introduced matches
  X, L = codom(rmap), pattern(static)
  new_matches, new_keys = Dict{Int, ACSetTransformation}(), Pair{Int,Int}[]

  push!(runtime.match_vect, new_matches)
  old_stuff = Dict(o => setdiff(parts(X,o), collect(rmap[o])) for o in ob(S))
  seen_constraints = Set() # non-monic match can identify different subobjects 
  for (idx, (subL, mapR)) in enumerate(static.overlaps[i])
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
      for h in homomorphisms(L, X; monic=constraints.monic, initial, predicates)
        if h ∈ values(new_matches) # this could be skipped once code is trusted
          error("Duplicating work $h")
        else # PAC?
          @debug "NEW from $subL\n$mapR"
          new_key = length(runtime) => length(new_keys)+1
          push!(key_vect(runtime), new_key)
          push!(new_keys, new_key)
          key_dict(runtime)[new_key] = length(key_vect(runtime))
          new_matches[length(new_keys)] = h 
        end
      end
    end
  end
  set_state!(runtime, X)
  return (invalidated_keys, new_keys)
end

"""
Delete / modify existing matches based on the target ACSet being permuted or 
reduced to a subobject. If a match touches upon something which is deleted, 
remove the match. Given X ↩ X′ we are updating Hom(L, X) => Hom(L, X′)

In the presence of negative application conditions / dangling condition, 
a deletion can also *add* new matches.

Returns the 'keys' of the deleted matches and added matches.
"""
deletion!(hset::IncHomSet, f::ACSetTransformation) = deletion!(hset..., f)

function deletion!(::IncCCStatic, runtime::IncCCRuntime, constr::IncConstraints,  
                   f::ACSetTransformation)
  invalidated_keys = Pair{Int,Int}[]
  for (idx, dic) in enumerate(match_vect(runtime))
    for (idx′, m) in collect(dic)
      m′ = pull_back(f, m)
      # Delete if match refers to something deleted OR we have invalidated a PAC
      if isnothing(m′) || !can_match(constr, m′; nac=false)
        delete!(dic, idx′)
        delete!(key_dict(runtime), idx => idx′)
        push!(invalidated_keys, idx => idx′)
      else 
        dic[idx′] = m′
      end
    end
  end

  set_state!(runtime, dom(f))

  # A NAC has been deactivated if there exists a morphism N ⇾ X that sends 
  # all of L to the nondeleted part of X and *some* of N to the deleted portion.
  new_matches, new_keys = Dict{Int, ACSetTransformation}(), Pair{Int,Int}[]
  push!(runtime.match_vect, new_matches)
  for n in constr.nac
    for h in homomorphisms(codom(n), state(runtime); monic=n.monic)
      if can_match(constr, h; pac=true)
        new_key = length(runtime) => length(new_keys)+1
        push!(key_vect(runtime), new_key)
        push!(new_keys, new_key)
        key_dict(runtime)[new_key] = length(key_vect(runtime))
        new_matches[length(new_keys)] = h 
      end
    end
  end
  return (invalidated_keys, new_keys)
end

"""
Given f: L->X and m: X' ↣ X, find the unique map L -> X' making the triangle 
commute, if it exists.

TODO rewrite with @comptime
"""
function pull_back(f::ACSetTransformation, m::ACSetTransformation
                  )::Union{ACSetTransformation, Nothing}
  L, X′ = dom.([m, f])
  comps, S = Dict(), acset_schema(L)
  for o in ob(S)
    vec = []
    for i in parts(L, o)
      pre = preimage(f[o], m[o](i))
      length(pre) == 1 || return nothing
      push!(vec, only(pre))
    end
    comps[o] = vec
  end
  for o in attrtypes(S)
    comps[o] = map(AttrVar.(parts(L, o))) do i 
      for (f, c, _) in attrs(S; to=o)
        inc = incident(L, i, f)
        isempty(inc) || return X′[comps[c][first(inc)], f]
      end
    end
  end
  ACSetTransformation(dom(m), dom(f); comps...)
end

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
                 ) where T
  # Check input data
  c_err = compat_constraints(constraints(hset), r) 
  isnothing(c_err) || error("Constraint mismatch: $c_err")
  i = findfirst(==(right(r)), additions(hset)) # RHS of rule must be an addition
  state(hset) == codom(match)|| error("Codom mismatch for match $match")

  # Perform rewrite, unpack results
  rw_result = rewrite_match_maps(r, match)
  del_map, pushforward_no_attr = get_pmap(T, rw_result)
  pushforward_attr = get_expr_binding_map(r, match, rw_result)
  pushforward = pushforward_no_attr ⋅ pushforward_attr
  rmap = get_rmap(T, rw_result) ⋅ pushforward_attr

  # Use results to update hom set
  del_invalidated, del_new = deletion!(hset, del_map)
  add_invalidated, add_new = addition!(hset, i, rmap, pushforward)
  (vcat(del_invalidated, add_invalidated), vcat(del_new, add_new))
end

"""Perform a pushout addition given a match morphism from the domain."""
addition!(hset::IncHomSet, i::Int, omap::ACSetTransformation) =
  addition!(hset, i, pushout(additions(hset)[i], omap)...)

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
