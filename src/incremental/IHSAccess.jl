module IHSAccess 

export rules, validate, state, states, matches, nmatches, qrules, decomp_dict, 
  get_cases, decomp_match, get_match, interaction_square

using DataStructures: DefaultDict
using Catlab 
import Catlab: acset_schema, validate

using ..IHSData: IHS, distinguished_object
import ....Rewrite: get_match, pattern

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
    h[r, :profile] == empty_profile(h) && h[r, :qrule] ≃ f
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
  cat = infer_acset_cat(S)
  updates = h[incident(h, iₛ, :update_state), :update_comp]
  curr = h[iₛ, :curr]
  feet_matches = map(dom.(legs(colim))) do X
    map(cc_matches(h, iₛ, pattern_cc(h, X))) do match_id
      cmps = Dict(map(collect(pairs(h[match_id, :match]))) do (k,v)
        rest = [updates[time][k] for time in (h[match_id, :match_time]+1):curr]
        k => foldl(compose[FinSetC()], [v; rest])
      end )
      m = ACSetTransformation(X, S; cmps...)
      is_natural(m) || error("Bad m $m")
      m
    end
  end
  map(Iterators.product(feet_matches...)) do combo
    @withmodel cat (universal, ⋅) begin 
      force(h[iₚ, :pattern_iso] ⋅ universal(colim, Multicospan(S, collect(combo))))
    end
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
Return a user-friendly dictionary summarizing the total scenarios that get 
looped over.

Note that a single decomposition can include both quotiented and unquotiented 
versions of a rule. Set `quotient=false` to only allow decompositions in which 
all rules are unquotiented.
"""
function get_cases(h::IHS, pat=nothing, rule=nothing; batch=true, 
                  quotient=true)
  res = []
  ep = empty_profile(h)

  isnothing(pat) || error("Restricting to a single pattern not yet supported")
  isnothing(rule) || error("Restricting to a single rule not yet supported")
  nparts(h, :Pattern) == nparts(h, :Rule) == 1 || error("Must be unique")

  good_ints = _get_nonredundant_interactions(h, quotient)
  for decomp in parts(h, :Decomp)
    old_id, colim, iso = [h[decomp, fk] for fk in [:decomp_tgt, :decomp_colim, :decomp_iso]]
    old = h[old_id, :subobj]
    elems = incident(h, decomp, :decomp)
    batch || length(elems) == 1 || continue 
    interaction_sets = map(elems) do elem 
      key = (h[elem, :decomp_elem_L], h[elem, :decomp_elem_R], 1)
      get(good_ints, key, []) 
    end
    for int_combo in Iterators.product(interaction_sets...)
      decomps = map(zip(elems,int_combo)) do (elem, int)
        qrule_id, L_id, R_id = h[int, :i_rule], h[int, :idata_L], h[int, :idata_R]
        QL, QR = h[[L_id, R_id], :subobj]
        quot, rule_id, qrule = [h[qrule_id, fk] for fk in [:profile ,:rule, :qrule]]
        rule = h[only(incident(h, rule_id, :rule) ∩ incident(h, ep, :profile)), :qrule]
        LR = subobj_incl(h, L_id,R_id)
        hL, hR = h[int, :idata_iL], h[int, :idata_iR]

        # integrity checks
        @assert dom(LR) == dom(QL) "$(dom(LR))\n$QL"
        @assert codom(LR) == dom(QR)
        @assert dom(hL) == dom(QL)
        @assert dom(hR) == dom(QR)
        @assert codom(hL) == dom(qrule)
        @assert codom(hR) == codom(qrule)

        (; rule, quot, qrule, QL, QR, LR, hL, hR)
      end |> (batch ? identity : only)
      push!(res, (; old, colim, iso, decomps))
    end
  end
  res 
end


"""
Check whether (f,h) is the pullback of (g,i) for f:A→B, g:B→D, h:A→C, i:C→D
"""
function is_pullback(𝒞, f,g,h,i)
  @withmodel 𝒞 (pullback, universal, is_epic, is_monic, ⋅) begin
    π1, π2 = po = pullback(g, i)
    σ = universal(po, Span(f, h))
    is_epic(σ) && is_monic(σ) || return false
    force(σ⋅π1) == force(f) || return false 
    force(σ⋅π2) == force(h)
  end
end

""" 
Check whether a square f⋅g=h⋅i is a pullback by checking it is pointwise a 
pullback.
""" 
function is_cset_pullback(f::ACSetTransformation,g::ACSetTransformation,
                          h::ACSetTransformation,i::ACSetTransformation)
  dom(g) == codom(f) || error()
  dom(i) == codom(h) || error()
  dom(f) == dom(h) || error()
  codom(g) == codom(i) || error()
  all(ob(acset_schema(f))) do o 
    is_set_pullback(f[o],g[o],h[o],i[o])
  end
end

""" 
Check whether a square f⋅g=h⋅i is a pullback by checking it is pointwise a 
pullback.
""" 
function is_set_pullback(f::FinFunction, g::FinFunction, h::FinFunction, i::FinFunction)
  dic1,dic2 = [DefaultDict{Any,Int}(()->0) for _ in 1:2]
  for x in dom(f)
    dic1[f(x)=>h(x)]+=1
  end
  for x in dom(g)
    for y in preimage(i, g(x))
      dic2[x=>y]+=1
    end
  end
  dic1 == dic2
end

"""
A good interaction (QL,QR,L,R,hL,hR,f) is one for which there does not exist
another interaction (QL,QR,L',R',hL',hR',f') for which there exist morphisms
qL:L'↠L, qR:R'↠R such that the pullback factors into two pullback squares.

Returns the interactions indexed by their (QL,QR,f::Rule) ids in the database.
"""
function _get_nonredundant_interactions(h::IHS, quotient::Bool=true)::Dict{Tuple{Int,Int,Int},Vector{Int}}
  @assert quotient # TODO filter to only use unquotiented rules
  𝒞 = infer_acset_cat(pattern(h))
  S = acset_schema(pattern(h))
  V = distinguished_object(S)
  # partition interactions by those with the same underlying rule and QL↣QR
  # and then further partition by which quotient of the rule they use
  ipartition = DefaultDict{Tuple{Int,Int,Int},DefaultDict{Int,Vector{Int}}}(
    ()->DefaultDict{Int,Vector{Int}}(()->Int[]))
  for int in parts(h, :Interaction)
    QL, QR, f, r = h[int,:idata_L], h[int,:idata_R], h[int, :i_rule], h[int, (:i_rule,:rule)]
    push!(ipartition[(QL,QR,r)][f], int)
  end
  # Cached computations 
  #--------------------
  epi_cache = Dict()
  epis(A::ACSet,B::ACSet) = if haskey(epi_cache, A=>B)
    epi_cache[A=>B]
  else 
    epi_cache[A=>B] = homomorphisms(A,B; epic=true) 
  end

  pb_cache = Dict()
  # Given f:L→R and f′:L′→R′, look for pairs of epis (qₗ:L′↠L, qᵣ:R′↠R) such that
  # f′⋅qᵣ==qₗ⋅f
  function epi_pb(f::ACSetTransformation,f′::ACSetTransformation) 
    L,R,L′,R′ = dom(f), codom(f), dom(f′), codom(f′)
    if haskey(epi_cache, (f′,f))
      pb_cache[(f′,f)]
    else 
      qs = collect(Iterators.product(epis(L′,L),epis(R′,R)))
      pb_cache[(f′,f)] = filter(((qₗ,qᵣ),)->is_cset_pullback(f′,qᵣ,qₗ,f), qs)
    end
  end
  
  good_ints = DefaultDict{Tuple{Int,Int,Int},Vector{Int}}(()->Int[])
  for (k, fdict) in pairs(ipartition)
    fs = sort(collect(keys(fdict)))
    f_homs =  h[fs, :qrule]
    for (i, f_id) in enumerate(fs)
      f = f_homs[i]
      for int in fdict[f_id]
        hₗ, hᵣ = h[int, :idata_iL], h[int, :idata_iR]
        # Look for interactions with f's which are MORE quotiented than i
        redundant = any(1:(i-1)) do j
          f′_id = fs[j]
          f′ = f_homs[j]
          any(epi_pb(f,f′)) do (qₗ, qᵣ)
            any(fdict[f′_id]) do int′
              hₗ′,hᵣ′ = h[int′, :idata_iL], h[int′, :idata_iR]
              # (hₗ ≃  hₗ′⋅qₗ) &&  (hᵣ ≃  hᵣ′⋅qᵣ)
              for i in parts(dom(hₗ), V)
                hₗ[V](i) == qₗ[V](hₗ′[V](i)) || return false 
              end 
              for i in parts(dom(hᵣ), V)
                hᵣ[V](i) == qᵣ[V](hᵣ′[V](i)) || return false 
              end
              return true
            end
          end
        end
        redundant && continue
        push!(good_ints[k], int)
      end
    end
  end
  good_ints
end


""" 
Do a case analysis that mixes monic and nonmonic matches but avoids unnecessary 
case splitting on possible equations between items in the pattern of a rule. 
"""
function case_analysis_nonmonic(ihs::IHS)
  qcases = get_cases(ihs; batch=true, quotient=true) 
  f = ihs[1, :qrule]
  𝒞 = ACSetCategory(state(ihs))
  filter(qcases) do case
    old_subobj, new_subobjs = case[:old], case[:decomps]
    # check if `case` is a quotient of `caseₒ`
    !any(qcases) do caseₒ
      old_subobjₒ, new_subobjsₒ = getindex.(Ref(caseₒ),[:old, :decomps])
      _,ruleₒ = pushout[𝒞](f,qₒ)
      # cases must share old subobject
      old_subobjₒ == old_subobj || return false
      # no duplicates between rewrites at same quotient level
      q == qₒ && return false
      # `qₒ` must be a bigger quotient than `q`, look to factor `qₒ=q⋅q′`
      qqs = homomorphisms(codom(qₒ), codom(q); epic=true)
      isempty(qqs) && return false 
      q′ = only(qqs)

      # Need to match up the interactions.
      length(new_subobjs) == length(new_subobjsₒ) || return false
      all(new_subobjs) do new_subobj 
        new_subobjₒ_idx = findall(new_subobjsₒ) do new_subobjₒ
          all([:L,:R,:LR]) do key 
            new_subobj[key] == new_subobjₒ[key]
          end || return false
          new_subobj[:hL] == force(compose[𝒞](new_subobjₒ[:hL],q′)) || return false 
          _,hr′ = po = pushout[𝒞](q′,ruleₒ);
          any(isomorphisms(apex(po), codom(new_subobj[:hR]))) do σ
            new_subobj[:hR] == force(compose[𝒞](new_subobjₒ[:hR], compose[𝒞](hr′,σ)))
          end
        end
        isempty(new_subobjₒ_idx) && return false
        length(new_subobjₒ_idx) > 1 && error("Unexpected")
        return true
      end
    end
  end
end


""" Given an `Interaction` id, return the interaction PB square """
function interaction_square(ihs::IHS, i::Int)
  LR = subobj_incl(ihs, ihs[i,:idata_L], ihs[i,:idata_R])
  f = ihs[i, (:i_rule, :qrule)]
  f, ihs[i, :idata_iL], ihs[i, :idata_iR], LR
end

function check_decompositions(ihs::IHS)
  for d in parts(ihs, :Decomp)
    colim = ihs[d, :decomp_colim]
    cd = getvalue(colim.diagram)
    elems = incident(ihs, d, :decomp)
    @assert elems == sort(elems) # we assume elems are in order

    for (o1, L) in zip(ob₁(cd), ihs[elems, :decomp_elem_L] )
      @assert o1 == dom(ihs[L,:subobj]) "$o1 \n≠\n $(dom(ihs[L,:subobj]))"
    end

    @assert ob₂(cd)[1] == dom(ihs[d, (:decomp_tgt,:subobj)])

    for (o2, R) in zip(ob₂(cd)[2:end], ihs[elems, :decomp_elem_R] )
      @assert o2 == dom(ihs[R,:subobj])  "$o2 \n≠\n $(dom(ihs[R,:subobj]))"
    end
  end
end 
function check_interactions(ihs::IHS)
  for i in parts(ihs, :Interaction)
      LR = subobj_incl(ihs, ihs[i,:idata_L], ihs[i,:idata_R])
      f = ihs[i, (:i_rule, :qrule)]
      𝒞 = infer_acset_cat(f)
      @assert is_cset_pullback(LR, ihs[i, :idata_iR],ihs[i, :idata_iL], f)
      @assert is_pullback(𝒞, LR, ihs[i, :idata_iR],ihs[i, :idata_iL], f)
  end
end


""" Given a `Match` id, return the decomposition that it corresponds to """
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
  cat = infer_acset_cat(A)
  res = filter(homomorphisms(dom(A), dom(B); monic=true, cat)) do ab 
    force(A) == force(compose[cat](ab, B))
  end
  isempty(res) ? nothing : only(res)
end

subobj_lt(X::Subobject{<:ACSet}, Y::Subobject{<:ACSet}) = 
  subobj_lt(hom(X), hom(Y))

subobj_lt(A::ACSetTransformation, B::ACSetTransformation) = 
  !isnothing(subobj_incl(A,B))

subobj_eq(X::Subobject{<:ACSet}, Y::Subobject{<:ACSet}) = 
  subobj_eq(hom(X), hom(Y))

subobj_eq(A::ACSetTransformation, B::ACSetTransformation) = 
  all(ob(acset_schema(A))) do o 
    Set(collect(A[o])) == Set(collect(B[o]))
  end

end # module
