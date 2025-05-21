module IHSAccess 

export rules, validate, state, states, matches, nmatches, qrules, decomp_dict, 
  get_interactions, decomp_match, get_match, interaction_square

using DataStructures: DefaultDict
using Catlab 
import Catlab: acset_schema

using ..IHSData: IHS
import ....Rewrite: get_match

# Pattern access 
################

patterns(i::IHS)::AbstractVector = parts(i, :Pattern)
""" Get the Pattern id of the only pattern - throw error if there are more """
pattern(h::IHS) = pattern(h, only(patterns(h)))

""" Get the Pattern (as an ACSet) based on Pattern id """
pattern(h::IHS, i::Int)::ACSet = h[i, :pattern]

subobjs(h::IHS, pat_cc::Int) = incident(h, pat_cc, :subpattern)
decomps(h::IHS, subobj_id::Int) = incident(h, subobj_id, :decomp_tgt)
decomp_elems(h::IHS, decomp_id::Int) = incident(h, decomp_id, :decomp)

decomp_dict(h::IHS, pat_cc::Int) = Dict(map(subobjs(h, pat_cc)) do iₚ
  iₚ => map(decomps(h,iₚ)) do i 
    h[decomp_elems(h, i), :decomp_src]
  end 
end)

decomp_dict(h::IHS) = decomp_dict(h, only(pattern_ccs(h)))


# Rule access
#############

""" Get the (unquotiented) rule id """
function rule(h::IHS, f::ACSetTransformation)::Int
  h[only(filter(parts(h, :QRule)) do r 
    h[r, :profile] == empty_profile(h) && h[r, :qrule] == f
  end), :rule]
end

qrules(i::IHS) = parts(i, :QRule)

pattern_ccs(h::IHS)::AbstractVector = parts(h, :PatternCC)
pattern_cc(h::IHS, i::Int)::ACSet = h[i, :pattern_cc]
# CC patterns are NOT canonicalized. The colim picks a canonical isomorph
pattern_cc(h::IHS, X::ACSet)::Int = only(incident(h, X, :pattern_cc))

underlying_acset_schema(i::IHS) = acset_schema(pattern_cc(i,1))

empty_profile(i::IHS) = 
  Dict(k => Set{Set{Int}}() for k in ob(underlying_acset_schema(i)))

# State access
##############

states(h::IHS)::AbstractVector = parts(h, :State)
state(h::IHS)::ACSet = state(h, only(states(h))) 
state(h::IHS, i::Int)::ACSet = h[i, :state]

curr(h::IHS, s::Int) = h[s, :curr]

""" Get all interactions for a given pattern (subobject) ID and a (quotiented) rule ID. """
function interactions(h::IHS, iₚ::Int,iᵣ::Int)
  iₚᵣ = only(incident(h, iₚ, :πpat) ∩ incident(h, iᵣ, :πrule))
  incident(h, iₚᵣ, :patrule)
end

# Getting matches
#################
function get_match(i::IHS, iₘ::Int) 
  comps, G = i[iₘ, :match], i[iₘ, (:match_state, :state)]
  X = i[get_match_pattern(i, iₘ), :pattern_cc]
  ACSetTransformation(comps, X, G)
end

""" Take a Match index and get a PatternCC index """
function get_match_pattern(ihs::IHS, iₘ::Int)::Int
  i = incident(ihs, iₘ, :initial_match)
  !isempty(i) && return ihs[only(i),(:match_pattern, :pattern_cc)]
  i = incident(ihs, iₘ, :created_match)
  !isempty(i) && return ihs[first(incident(ihs, only(i), :matchdecomp_match)),
                            (:matchdecomp_interaction, :idata_L, :subpattern)]
  error("Need to cover other cases $iₘ")
end

matches(i::IHS, X::ACSet) = matches(i, pattern(X))

matches(h::IHS) = matches(h, only(states(h)), only(patterns(h)))

"""
Get matches for connected components, then take their product
"""
function matches(h::IHS, iₛ::Int, iₚ::Int)
  colim = h[iₚ, :pattern_coprod]
  S = state(h, iₛ)
  feet_matches = map(dom.(legs(colim))) do X
    map(h[cc_matches(h, iₛ, pattern_cc(h, X)), :match]) do cmps
      m = ACSetTransformation(X, S; cmps...)
      is_natural(m) || error("Bad m $m")
      m
    end
  end
  map(Iterators.product(feet_matches...)) do combo
    h[iₚ, :pattern_iso] ⋅ universal(colim, Multicospan(S, collect(combo)))
  end
end

""" 
Matches into a state for a particular connected component 

These come from one of two sources. Initial matches or CreatedMatches.
(Also from CreatedMatch)
"""
function cc_matches(h::IHS, iₛ::Int, cc::Int)
  mₛ = incident(h, iₛ, :match_state)
  mz = h[incident(h, cc, :match_pattern), :initial_match]
  m3 = h[incident(h, cc, (:matchdecomp_interaction, :idata_L, :subpattern)), (:matchdecomp_match, :created_match)]
  mₛ ∩ (mz ∪ m3)
end

""" Total number of matches for a pattern """
nmatches(h::IHS, iₚ::Int)::Int =
  prod(length.(feet_matches(h, iₚ)))

# Validation
############

function validate(hset::IHS)::Bool
  for p in patterns(hset)
    X = pattern(hset, p)
    for s in states(hset)
      S = hset[s, :state]
      ms = matches(hset,s,p)
      length(ms) == length(Set(ms)) || error("Matches not unique")
      all(is_natural, ms) || error("Unnatural")
      all(==(X), dom.(ms)) || error("Bad dom")
      all(==(S), codom.(ms)) || error("Bad codom")
      ref = Set(homomorphisms(X, S))
      xtra = setdiff(ms, ref)
      missin = setdiff(ref, ms)
      isempty(xtra ∪ missin) || error("\n\textra $xtra \n\tmissing $missin")
    end
  end
  true
end

# User friendly methods
#######################

"""
Optionally filter by interactions based on a particular pattern, subpattern,
and/or rule. By default ignore quotients of rules. Ignore trivial interactions 
(where subobj = identity).
"""
function get_interactions(h::IHS; pat=nothing, subpat=nothing, rule=nothing)
  res = []
  for pr in parts(h, :SubobjQRule)
    subpattern_id, qrule_id = h[pr, :πpat],h[pr, :πrule]
    subpattern = h[subpattern_id, :subobj]
    is_epic(subpattern) && continue
    pattern = h[subpattern_id, (:subpattern, :pattern_cc)]
    isnothing(subpat) || subpat == subpattern || continue
    isnothing(pat) || pat == pattern || continue 

    isnothing(rule) || rule == h[qrule_id, :qrule] || continue
    for interaction_id in incident(h, pr, :patrule)
      iL, iR = h[interaction_id, :iL], h[interaction_id, :iR]
      push!(res, (;subpattern_id, qrule_id, interaction_id, 
                 subpattern=Subobject(subpattern), rule=h[qrule_id, :qrule], 
                 iL, iR))
    end
  end
  res 
end

function interaction_square(ihs::IHS, i::Int)
  LR = subobj_incl(ihs, ihs[i,:idata_L], ihs[i,:idata_R])
  f = ihs[i, (:i_rule, :qrule)]
  f, ihs[i, :idata_iL], ihs[i, :idata_iR], LR
end

function decomp_match(ihs::IHS, iₘ::Int)
  S = ihs[iₘ, (:match_state, :state)]
  match_decomps = incident(ihs, iₘ, (:matchdecomp_match, :created_match))
  ints = ihs[match_decomps, :matchdecomp_interaction]
  XR_idxs = ihs[ints, :idata_R]
  XRs = dom.(ihs[XR_idxs, :subobj])
  res = DefaultDict(()->[])
  for (int, XR, d) in zip(ints, XRs, match_decomps)
    push!(res[int], ACSetTransformation(ihs[d, :matchdecomp_hom], XR, S))
  end
  res
end

# Comparing subobjects
#----------------------

subobject(ihs::IHS, i::Int) = ihs[i, :subobj]
subobj_incl(ihs::IHS, i::Int, j::Int) = subobj_incl(subobject(ihs,i), subobject(ihs, j))

subobj_incl(As::Vector, i::Int, j::Int) = subobj_incl(As[i], As[j])

subobj_incl(X::Subobject{<:ACSet}, Y::Subobject{<:ACSet}) = 
  subobj_incl(hom(X), hom(Y))

""" Given a A ↣ X ↢ B, get A ↣ B (if it exists) """
function subobj_incl(A::ACSetTransformation, B::ACSetTransformation)
  res = filter(homomorphisms(dom(A), dom(B); monic=true)) do ab 
    force(A) == force(ab ⋅ B)
  end
  isempty(res) ? nothing : only(res)
end

subobj_lt(X::Subobject{<:ACSet}, Y::Subobject{<:ACSet}) = 
  subobj_lt(hom(X), hom(Y))

subobj_lt(A::ACSetTransformation, B::ACSetTransformation) = 
  !isnothing(subobj_incl(A,B))

end # module
