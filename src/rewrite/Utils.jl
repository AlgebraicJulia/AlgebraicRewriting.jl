module Utils

export Rule, ruletype,rewrite, rewrite_match, rewrite_full_output, 
       rewrite_match_maps, can_match, get_match, get_matches

using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.CSets: backtracking_search
import Catlab.CategoricalAlgebra: left, right

using Random
using StructEquality

using ..Constraints
using ...CategoricalAlgebra
using ...CategoricalAlgebra.CSets: invert_hom


# RULES 
#######
abstract type AbsRule end 

"""
Rewrite rules which are (usually) encoded as spans. 
The L structure encodes a pattern to be matched. 
The R morphism encodes a replacement pattern to be substituted in.
They are related to each other by an interface I with maps: L ⟵ I ⟶ R 

A semantics (DPO, SPO, or SqPO) must be chosen.

Control the match-finding process by specifying whether the match is
intended to be monic or not, as well as an optional application
condition(s) 
"""
@struct_hash_equal struct Rule{T} <: AbsRule
  L::Any
  R::Any
  conditions::Vector{Constraint} # constraints on match morphism
  monic::Union{Bool, Vector{Symbol}} # further constraint on match morphism
  exprs::Dict{Symbol, Dict{Int,Union{Nothing,Function}}}

  function Rule{T}(L, R; ac=nothing, monic=false, expr=nothing, freevar=false) where {T}
    dom(L) == dom(R) || error("L<->R not a span")
    ACs = isnothing(ac) ? [] : ac
    exprs = isnothing(expr) ? Dict() : Dict(pairs(expr))
    map(enumerate([L,R,])) do (i, f)
      if !is_natural(f)
        error("unnatural map #$i: $f")
      end
    end
    for (i,cond) in enumerate(ACs)
      λ = findfirst(==(1), cond.g[:elabel])
      λv = cond.g[λ, :src]
      λs = cond.g[λv,:vlabel]
      err = "Condition $i: source $λs \n != match L $(codom(L))\nE#$λ V#$λv"
      λs == codom(L) || error(err)
    end 
    # For the case of ACSet rewriting, address variable substitution in R
    if !(dom(L) isa ACSet)
      exprs = Dict()
    else 
      exprs = Dict(map(attrtypes(acset_schema(dom(L)))) do o
        binding = Dict()
        for r_var in parts(codom(R),o)
          # User explicitly provides a function to evaluate for this variable
          if !isnothing(expr) && haskey(expr, o) && r_var ∈ keys(expr[o])
            binding[r_var] = expr[o][r_var]
          else # try to see if the value is determined by the partial map
            preim = preimage(R[o],AttrVar(r_var))
            pr = unique(L[o].(AttrVar.(preimage(R[o],AttrVar(r_var)))))
            if length(pr) == 1 
              binding[r_var] = vs -> vs[only(pr).val] 
            elseif freevar # We are ok with introducing free variables
              continue 
            else 
              error("Unbound variable in R $o#$r_var")
            end 
          end
        end
        o => binding
      end)
    end
    new{T}(L, R, ACs, monic, exprs)
  end
end

Rule(l, r; kw...) = Rule{:DPO}(l, r; kw...)
ruletype(::Rule{T}) where T = T
left(r::Rule{T}) where T = r.L
right(r::Rule{T}) where T = r.R

(F::Migrate)(r::Rule{T}) where {T} =
  Rule{T}(F(r.L), F(r.R); ac=F.(r.conditions), expr=F(r.exprs), monic=r.monic)

# Extracting specific maps from rewriting output data 
#####################################################

"""Extract the map from the R to the result from the full output data"""
function get_rmap(sem::Symbol, maps)
  if isnothing(maps)  nothing
  elseif sem == :DPO  maps[:rh]
  elseif sem == :SPO  invert_hom(maps[:rmono], epic=false) ⋅ maps[:rmap]
  elseif sem == :SqPO maps[:r]
  elseif sem == :PBPO maps[:w]
  else   error("Rewriting semantics $sem not supported")
  end
end

get_result(sem::Symbol, maps) = codom(get_rmap(sem, maps))

"""Extract the partial map (derived rule) from full output data"""
function get_pmap(sem::Symbol, maps)
  if isnothing(maps)  nothing
  elseif sem == :DPO  Span(maps[:kg], maps[:kh])
  elseif sem == :SPO  Span(maps[:gmono], maps[:gmap])
  elseif sem == :SqPO Span(maps[:i], maps[:o])
  elseif sem == :PBPO Span(maps[:gl], maps[:gr])
  else   error("Rewriting semantics $sem not supported")
  end
end

# Match finding
################
check_initial(vs::Vector{Int}, f::Vector{Int}) =
  [(i, vs[i], f[i]) for i in length(f) if vs[i]!=f[i]]
check_initial(vs::Vector{Pair{Int,Int}}, f::Vector{Int}) =
  [(i,f[i],v) for (i,v) in vs if f[i]!=v]

# Check if a component is included in a monic constraint
has_comp(monic::Bool, c::Symbol) = monic
has_comp(monic::Vector{Symbol}, c::Symbol) = c ∈ monic

"""
Returns nothing if the match is acceptable for rewriting according to the
rule, otherwise returns the reason why it should be rejected
"""
function can_match(r::Rule{T}, m; initial=Dict()) where T
  S = acset_schema(dom(m))
  for k in ob(S)
    if has_comp(r.monic,k) && !is_monic(m[k])
      return ("Match is not injective", k, m[k])
    end
  end
  for (k, vs) in collect(initial)
    errs = check_initial(vs, collect(m[k]))
    if !isempty(errs)
      return ("Initial condition violated",k, errs)
    end
  end

  is_natural(m) || return ("Match is not natural", m)

  if T == :DPO
    gc = gluing_conditions(ComposablePair(r.L, m))
    if !isempty(gc)
      return ("Gluing conditions failed", gc)
    end
  end

  for (nᵢ, N) in enumerate(r.conditions)
    if !apply_constraint(N, m)
      return ("Constraint $nᵢ failed", nᵢ)
    end
  end

  return nothing # we can match
end

get_match(args...; kw...) = let x = get_matches(args...; n=1, kw...);
  isempty(x) ? nothing : only(x) end 

"""
Get list of possible matches based on the constraints of the rule

This function has the same behavior as the generic `get_matches`, but it is 
more performant because we do not have to query all homomorphisms before finding 
a valid match, in case n=1. 
"""
function get_matches(r::Rule{T}, G::ACSet; initial=nothing,
                     random=false, n=-1) where T
  initial = isnothing(initial) ? Dict() : initial

  hs = []
  backtracking_search(codom(r.L), G; monic=r.monic, initial=NamedTuple(initial), 
                      random=random) do h 
    cm = can_match(r,h)
    if isnothing(cm)
      push!(hs, deepcopy(h))
      return length(hs) == n # we stop the search Hom(L,G) when this holds
    else
      @info "$([k => collect(v) for (k,v) in pairs(components(h))]): $cm"
      return false
    end
  end 
  return hs
end

"""If not rewriting ACSets, we have to compute entire Hom(L,G)."""
function get_matches(r::Rule{T}, G; initial=nothing, random=false, n=-1) where T 
  initial = isnothing(initial) ? Dict() : initial
  ms = homomorphisms(codom(left(r)), G; monic=r.monic, 
                     initial=NamedTuple(initial), random=random)
  res = []
  for m in ms 
    if (n < 0 || length(res) < n) && isnothing(can_match(r, m))
      push!(res, m)
    end
  end
  return res
end 

# Variables
###########

"""Get a list of AttrVar indices which are NOT bound by the I→R morphism"""
function freevars(r::Rule{T}, attrvar::Symbol) where T
  setdiff(parts(codom(r.R), attrvar), 
          [v.val for v in collect(r.R[attrvar]) if v isa AttrVar])
end 

"""
Given the match morphism and the result, construct a map X → X′ which 
binds any free variables introduced into the result.

  L <- I -> R 
m ↓    ↓    ↓ res
  G <- • -> X 
            ↓  
            X′

"""
function get_expr_binding_map(r::Rule{T}, m::ACSetTransformation, res) where T
  X = codom(get_rmap(ruletype(r),res))
  comps = Dict(map(attrtypes(acset_schema(X))) do at 
      bound_vars = Vector{Any}(collect(m[at]))
      binding = Dict()
      for prt in parts(X,at)
        if haskey(r.exprs[at],prt)
          binding[prt] = r.exprs[at][prt](bound_vars)
        end 
      end
      return at => binding
  end)
  return sub_vars(X, comps)
end

"""Don't bind variables for things that are not ACSets"""
get_expr_binding_map(r::Rule{T}, m, X) where T =  id(get_result(ruletype(r), X))


# Rewriting functions that just get the final result
####################################################

function rewrite_match_maps end  # to be implemented for each T

"""    rewrite(r::Rule, G; kw...)
Perform a rewrite (automatically finding an arbitrary match) and return result.
"""
function rewrite(r::AbsRule, G; initial=nothing, random=false, kw...)
  m = get_match(r, G; initial=initial, random=random)
  return isnothing(m) ? nothing : rewrite_match(r, m; kw...)
end


"""    rewrite_match(r::Rule, m; kw...)
Perform a rewrite (with a supplied match morphism) and return result.
"""
rewrite_match(r::AbsRule, m; kw...) =
  codom(get_expr_binding_map(r, m, rewrite_match_maps(r,m; kw...)))


# Rewriting function which return the maps, too
###############################################
"""    rewrite_full_output(r::Rule, G; initial=Dict(), kw...)
Perform a rewrite (automatically finding an arbitrary match) and return a tuple:
1.) the match morphism 2.) all computed data 3.) variable binding morphism
"""
function rewrite_full_output(r::AbsRule, G; initial=nothing, random=false,
                             n=-1, kw...) 
  T = ruletype(r)
  ms = get_matches(r,G,initial=initial, random=random, n=n)
  if isempty(ms)
    return nothing
  elseif random
    shuffle!(ms)
  end
  m = first(ms)
  rdata = rewrite_match_maps(r, m; kw...)
  return (m, rdata, codom(get_expr_binding_map(r, m, get_rmap(T, rdata))))
end

end # module
