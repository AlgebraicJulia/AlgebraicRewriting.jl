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

  function Rule{T}(l, r; cat=nothing, ac=nothing, monic=false, expr=nothing, freevar=false) where {T}
    cat = isnothing(cat) ? infer_acset_cat(l) : cat
    L, R, I, I′ = codom[cat](l), codom[cat](r), dom[cat](l), dom[cat](r)
    S = acset_schema(L)
    monic = monic isa Bool ? (monic ? ob(S) : []) : monic
    expr = isnothing(expr) ? Dict() : expr
    T==:SqPO || is_monic[cat](l) || error("Left leg must be monic $(components(l))")
    I == I′ || error("L<->R not a span")
    ACs = isnothing(ac) ? [] : deepcopy.(ac)
    exprs = isnothing(expr) ? Dict() : Dict(pairs(expr))
    for (lbl, f) in ["left"=>l, "right"=>r]
      is_natural(f;cat) || error("unnatural $lbl map: $f")
    end

    # Check the application conditions are maps out of L
    for (i,cond) in enumerate(ACs)
      λ = findfirst(==(1), cond.g[:elabel])
      λv = cond.g[λ, :src]
      λs = cond.g[λv,:vlabel]
      err = "Condition $i: source $λs \n != match L $(L)\nE#$λ V#$λv"
      λs == L || error(err)
    end 

    # For the case of ACSet rewriting, address variable assignment in R
    exprs = !(L isa ACSet) ? Dict() : Dict(map(attrtypes(S)) do o
      𝒟 = attr_cat(cat, o)
      binding = Dict()
      is_monic[𝒟](r[o]) || error("I→R AttrType component must be monic $(r[o])")
      for r_var in parts(R, o)
        preim = preimage(r[o], Left(r_var))
        x = get′(expr, o, r_var)
        if !isempty(preim) # the value of this attrvar is preserved
          isnothing(x) || error(
            "Cannot manually set AttrVar value for a preserved attribute")
        else # value of this attr is set explicitly (or a freevar is introduced)
          if !isnothing(x)
            binding[r_var] = x
          elseif freevar continue 
          else 
            error(
            "Must set AttrVar value for newly introduced attribute via `exprs`")
          end
        end
      end
      o => binding
    end)
    new{T}(deepcopy(l), deepcopy(r), ACs, monic, exprs)
  end
end

get′(d::Union{NamedTuple,AbstractDict}, o::Symbol, i::Int) =  
  haskey(d, o) && haskey′(d[o], i) ? d[o][i] : nothing 
haskey′(d::AbstractDict{Int}, k::Int) = haskey(d, k) 
haskey′(d::AbstractVector, k::Int) = length(d) ≥ k 

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
function get_rmap(sem::Symbol, maps; cat)
  if isnothing(maps)  nothing
  elseif sem ∈ DPO′  maps[:rh]
  elseif sem == :SPO  compose[cat](invert_hom(maps[:rmono], epic=false), maps[:rmap])
  elseif sem == :SqPO maps[:r]
  elseif sem == :PBPO maps[:w]
  else   error("Rewriting semantics $sem not supported")
  end
end

get_result(sem::Symbol, maps; cat) = codom[cat](get_rmap(sem, maps; cat))

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
function can_match(r::Rule{T}, m; cat, homsearch=false, initial=Dict()) where T
  S = acset_schema(dom[cat](m))
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
    is_natural(m; cat) || return ("Match is not natural", m)
  end

  if T == :DPO
    gc = pushout_complement_violations[cat](ComposablePair(r.L, m; cat))
    if !isempty(gc)
      return ("Gluing conditions failed", gc)
    end

    # meq = check_match_var_eqs(r, m)
    # if !isempty(meq)
    #   return ("Induced attrvar equation failed", meq)
    # end
  end

  for (nᵢ, N) in enumerate(r.conditions)
    if !apply_constraint(N, m; cat)
      return ("Constraint $nᵢ failed", nᵢ)
    end
  end

  return nothing # we can match
end

"""Get one match (if any exist) otherwise return """
get_match(args...; cat, kw...) = let x = get_matches(args...; cat, take=1, kw...);
  isempty(x) ? nothing : only(x) end 

"""
Get list of possible matches based on the constraints of the rule

This function has the same behavior as the generic `get_matches`, but it is 
more performant because we do not have to query all homomorphisms before finding 
a valid match, in case n=1. 
"""
function get_matches(r::Rule, G::ACSet; cat=nothing, kw...) 
  cat = isnothing(cat) ? infer_acset_cat(G) : cat
  homomorphisms(codom(r.L), G; cat, kw..., monic=r.monic, 
                filter= m -> isnothing(can_match(r, m; cat, homsearch=true)))
end

"""If not rewriting ACSets, we have to compute entire Hom(L,G)."""
function get_matches(r::Rule, G; cat, take=nothing, kw...)
  ms = homomorphisms(codom[cat](left(r)), G; cat, kw..., monic=r.monic)
  res = []
  for m in ms 
    if (isnothing(take) || length(res) < take) && isnothing(can_match(r, m; cat))
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
function get_expr_binding_map(r::Rule{T}, m::ACSetTransformation, res; cat) where T
  rmap = get_rmap(T, res; cat)
  X = codom[cat](rmap)
  comps = Dict(map(attrtypes(acset_schema(X))) do at 
      atfun = hom_map[attr_cat(cat, at)](m[at])
      bound_vars = Vector{Any}(map(parts(dom(m), at)) do i 
        atfun(Left(i))
      end) 
      rfun = hom_map[attr_cat(cat, at)](rmap[at])
      at => Dict(rfun(Left(i)).val => xpr(getvalue.(bound_vars)) 
                 for (i, xpr) in r.exprs[at])
  end)
  sub_vars(X, comps; cat)
end

"""Don't bind variables for things that are not ACSets"""
get_expr_binding_map(r::Rule{T}, m, X; cat) where T = 
  id[cat](get_result(ruletype(r), X; cat))


# Rewriting functions that just get the final result
####################################################

function rewrite_match_maps end  # to be implemented for each T

"""    rewrite(r::Rule, G; kw...)
Perform a rewrite (automatically finding an arbitrary match) and return result.
"""
function rewrite(r::AbsRule, G; cat=nothing, initial=(;), random=false, kw...)
  cat = isnothing(cat) ? infer_acset_cat(G) : cat
  m = get_match(r, G; cat, initial, random)
  isnothing(m) ? nothing : rewrite_match(r, m; cat, kw...)
end


"""    rewrite_match(r::Rule, m; kw...)
Perform a rewrite (with a supplied match morphism) and return result.
"""
function rewrite_match(r::AbsRule, m; cat=nothing, kw...) 
  cat = isnothing(cat) ? infer_acset_cat(m) : cat
  maps = rewrite_match_maps(r, m; cat, kw...)
  codom[cat](get_expr_binding_map(r, m, maps; cat))
end

function check_match_var_eqs end # implement in DPO.jl
end # module
