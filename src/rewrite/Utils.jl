module Utils

export Rule, ruletype,rewrite, rewrite_match, rewrite_full_output, 
       rewrite_match_maps, can_match, get_match, get_matches, pattern

using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.HomSearch: backtracking_search
import Catlab.CategoricalAlgebra: left, right
import ACSets: sparsify, acset_schema

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

A semantics (DPO, SPO, CoNeg, or SqPO) must be chosen.

Control the match-finding process by specifying whether the match is
intended to be monic or not, as well as an optional application
condition(s) 
"""
@struct_hash_equal struct Rule{T} <: AbsRule
  L::Any
  R::Any
  conditions::Vector{Constraint} # constraints on match morphism
  monic::Vector{Symbol} # further constraint on match morphism
  exprs::Dict{Symbol, Dict{Int,Union{Nothing,Function}}}

  function Rule{T}(L, R; ac=nothing, monic=false, expr=nothing, freevar=false) where {T}
    S = acset_schema(dom(L))
    monic = monic isa Bool ? (monic ? ob(S) : []) : monic
    dom(L) == dom(R) || error("L<->R not a span")
    ACs = isnothing(ac) ? [] : deepcopy.(ac)
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
      exprs = Dict(map(attrtypes(S)) do o
        binding = Dict()
        for r_var in parts(codom(R), o)
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
    new{T}(deepcopy(L), deepcopy(R), ACs, monic, exprs)
  end
end

Rule(X::ACSet; kw...) = Rule(id(X), id(X); kw...) # only changing attributes
Rule(l, r; kw...) = Rule{:DPO}(l, r; kw...) # Assume DPO by default
ruletype(::Rule{T}) where T = T
left(r::Rule{T}) where T = r.L
right(r::Rule{T}) where T = r.R
pattern(r::Rule) = codom(left(r))
acset_schema(r::Rule) = acset_schema(pattern(r))


(F::Migrate)(r::Rule{T}) where {T} =
  Rule{T}(F(r.L), F(r.R); ac=F.(r.conditions), expr=F(r.exprs), monic=r.monic)
sparsify(r::Rule{T}) where T = 
  Rule{T}(sparsify(r.L), sparsify(r.R); ac=sparsify.(r.conditions), 
          expr=r.exprs, monic=r.monic)

# Extracting specific maps from rewriting output data 
#####################################################
DPO′ = [:DPO, :CoNeg] # these have identical diagrams

"""Extract the map from the R to the result from the full output data"""
function get_rmap(sem::Symbol, maps)
  if isnothing(maps)  nothing
  elseif sem ∈ DPO′  maps[:rh]
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
  elseif sem ∈ DPO′   Span(maps[:kg], maps[:kh])
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
  [(i, f[i], v) for (i, v) in vs if f[i]!=v]

# Check if a component is included in a monic constraint
has_comp(monic::Bool, ::Symbol) = monic
has_comp(monic::Vector{Symbol}, c::Symbol) = c ∈ monic

"""
Returns nothing if the match is acceptable for rewriting according to the
rule, otherwise returns the reason why it should be rejected

homsearch = if we know ahead of time that m was obtained m via automatic hom 
            search, then we do not need to make certain checks
"""
function can_match(r::Rule{T}, m; homsearch=false, initial=Dict()) where T
  S = acset_schema(dom(m))
  if !homsearch
    for k in ob(S)
      if has_comp(r.monic, k) && !is_monic(m[k])
        return ("Match is not injective", k, m[k])
      end
    end
    for (k, vs) in collect(initial)
      errs = check_initial(vs, collect(m[k]))
      if !isempty(errs)
        return ("Initial condition violated", k, errs)
      end
    end
    is_natural(m) || return ("Match is not natural", m)
  end

  if T == :DPO
    gc = gluing_conditions(ComposablePair(r.L, m))
    if !isempty(gc)
      return ("Gluing conditions failed", gc)
    end

    meq = check_match_var_eqs(r, m)
    if !isempty(meq)
      return ("Induced attrvar equation failed", meq)
    end
  end

  for (nᵢ, N) in enumerate(r.conditions)
    if !apply_constraint(N, m)
      return ("Constraint $nᵢ failed", nᵢ)
    end
  end

  return nothing # we can match
end

"""Get one match (if any exist) otherwise return """
get_match(args...; kw...) = let x = get_matches(args...; take=1, kw...);
  isempty(x) ? nothing : only(x) end 

"""
Get list of possible matches based on the constraints of the rule

This function has the same behavior as the generic `get_matches`, but it is 
more performant because we do not have to query all homomorphisms before finding 
a valid match, in case n=1. 
"""
get_matches(r::Rule, G::ACSet; kw...) =
  homomorphisms(codom(r.L), G; kw..., monic=r.monic, 
                filter= m -> isnothing(can_match(r, m; homsearch=true)))

"""If not rewriting ACSets, we have to compute entire Hom(L,G)."""
function get_matches(r::Rule, G; take=nothing, kw...)
  ms = homomorphisms(codom(left(r)), G; kw..., monic=r.monic)
  res = []
  for m in ms 
    if (isnothing(take) || length(res) < take) && isnothing(can_match(r, m))
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
  rmap = get_rmap(T, res)
  X = codom(rmap)
  comps = Dict(map(attrtypes(acset_schema(X))) do at 
      bound_vars = Vector{Any}(collect(m[at]))
      binding = Dict()
      for prt in parts(X, at)
        exprs = filter(!isnothing, map(preimage(rmap[at], AttrVar(prt))) do rprt 
          get(r.exprs[at], rprt, nothing)
        end)
        if !isempty(exprs)
          
          binding[prt] = only(unique([expr(bound_vars) for expr in exprs]))
        end 
      end
      return at => binding
  end)
  sub_vars(X, comps)
end

"""Don't bind variables for things that are not ACSets"""
get_expr_binding_map(r::Rule{T}, m, X) where T =  id(get_result(ruletype(r), X))


# Rewriting functions that just get the final result
####################################################

function rewrite_match_maps end  # to be implemented for each T

"""    rewrite(r::Rule, G; kw...)
Perform a rewrite (automatically finding an arbitrary match) and return result.
"""
function rewrite(r::AbsRule, G; initial=(;), random=false, kw...)
  m = get_match(r, G; initial, random)
  isnothing(m) ? nothing : rewrite_match(r, m; kw...)
end


"""    rewrite_match(r::Rule, m; kw...)
Perform a rewrite (with a supplied match morphism) and return result.
"""
rewrite_match(r::AbsRule, m; kw...) =
  codom(get_expr_binding_map(r, m, rewrite_match_maps(r, m; kw...)))


function check_match_var_eqs end # implement in DPO.jl
end # module
