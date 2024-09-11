module Utils

export Rule, ruletype,rewrite, rewrite_match, rewrite_full_output, 
       rewrite_match_maps, can_match, get_match, get_matches, pattern

using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.CSets: sub_vars
using Catlab.CategoricalAlgebra.HomSearch: backtracking_search
import Catlab.CategoricalAlgebra: left, right
import ACSets: sparsify, acset_schema

using Random, DataStructures
using StructEquality

using ..Constraints
using ...CategoricalAlgebra
using ...CategoricalAlgebra.CSets: invert_hom, var_reference

import Catlab.CategoricalAlgebra.FinSets: is_monic
is_monic(f::SliceHom) = is_monic(f.f) # UPSTREAM


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

  function Rule{T}(l, r; ac=nothing, monic=false, expr=nothing, freevar=false) where {T}
    L, R, I, I′ = codom(l), codom(r), dom(l), dom(r)
    S = acset_schema(L)
    monic = monic isa Bool ? (monic ? ob(S) : []) : monic
    expr = isnothing(expr) ? Dict() : expr
    T==:SqPO || is_monic(l) || error("Left leg must be monic $(components(l))")
    I == I′ || error("L<->R not a span")
    ACs = isnothing(ac) ? [] : deepcopy.(ac)
    exprs = isnothing(expr) ? Dict() : Dict(pairs(expr))
    for (lbl, f) in ["left"=>l, "right"=>r]
      is_natural(f) || error("unnatural $lbl map: $f")
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
      binding = Dict()
      is_monic(r[o]) || error("I→R AttrType component must be monic $(r[o])")
      for r_var in parts(R, o)
        preim = preimage(r[o], AttrVar(r_var))
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
            "Must set AttrVar value for newly-introduced AttrVar $o#$r_var via `exprs` ($exprs)")
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


"""
Some rules involve deleting something and re-adding it. This means Σ
migrations can introduce variables in L and R that morally should be 
linked. If not linked, the rule will be invalid (due to introducing 
variables in R). This can be addressed by 'connecting' the variables via
adding AttrVars to I and mapping to the left and right. 

This is just a band-aid until patch-graph rewriting or something analogous 
allows us to avoid spurious deletion + addition rules.
"""
function (F::SimpleMigration)(r::Rule{T}; connect=true) where {T}
  expr = Dict(Symbol(ob_map(functor(F), k)) => v for (k,v) in pairs(r.exprs))
  Fl, Fr = F(r.L), F(r.R)
  FL, FR = codom(Fl), codom(Fr)
  S = acset_schema(FL)
  connect_dict = DefaultDict(()->[])
  if connect 
    for o in attrtypes(S)
      for r_var in parts(FR, o)
        preim = preimage(Fr[o], AttrVar(r_var))
        if isempty(preim) && isnothing(get′(expr, o, r_var))
          # Assume: new var is *not* floating
          (f, c, jᵣ) = var_reference(FR, o, r_var) 
          # Assume: part it's attached to uniquely identified w/ something in L
          jₗ = only([p for p in parts(FL, c) if isempty(preimage(Fl[c], p))])
          # And that thing has a fresh attrvar too
          if isempty(preimage(Fl[o], FL[jₗ, f]))
            p = add_part!(dom(Fl),o)
            p2 = add_part!(dom(Fr),o)
            p == p2 || error("p $p p2 $p2")
            push!(connect_dict[o], (p, FL[jₗ, f], AttrVar(r_var)))
          end
        end
      end
    end
  end 
  Fl, Fr = map([(Fl,1), (Fr,2)]) do (FMap, var)
    initial = Dict{Any,Any}(map(types(S)) do t 
      p(x::Int) = t ∈ ob(S) ? x : AttrVar(x)
      d =Dict{Any,Any}(map(connect_dict[t]) do (z, lr...)
        z => lr[var]
      end)
      for i in parts(dom(FMap), t)
        if !haskey(d, i)
          d[i] = FMap[t](p(i))
        end
      end
      t => d
    end)
    homomorphism(dom(FMap), codom(FMap); initial)
  end

  Rule{T}(Fl, Fr; ac=F.(r.conditions), expr, monic=r.monic)
end

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

    # meq = check_match_var_eqs(r, m)
    # if !isempty(meq)
    #   return ("Induced attrvar equation failed", meq)
    # end
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
      at => Dict(rmap[at](AttrVar(i)).val => xpr(bound_vars) 
                 for (i, xpr) in r.exprs[at])
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
