module RewriteUtils

export rewrite, rewrite_match, rewrite_parallel, rewrite_full_output,
       rewrite_match_maps, rewrite_parallel_maps, rewrite_sequential_maps

using Catlab, Catlab.Theories, Catlab.Schemas
using Catlab.CategoricalAlgebra
using Catlab.ColumnImplementations: AttrVar

using Random

using ...CategoricalAlgebra, ..RewriteDataStructures


# Extracting specific maps from rewriting output data 
#####################################################

"""Extract the map from the R to the result from the full output data"""
function get_rmap(sem::Symbol, maps)
  if isnothing(maps)  nothing
  elseif sem == :DPO  maps[:rh]
  elseif sem == :SPO  invert_hom(maps[:nb]) ⋅ maps[:nd]
  elseif sem == :SqPO maps[:r]
  elseif sem == :PBPO maps[:w]
  elseif sem == :AttrPBPO maps[:w]
  else   error("Rewriting semantics $sem not supported")
  end
end

get_result(sem::Symbol, maps) = codom(get_rmap(sem, maps))

"""Extract the partial map (derived rule) from full output data"""
function get_pmap(sem::Symbol, maps)
  if isnothing(maps)  nothing
  elseif sem == :DPO  Span(maps[:kg], maps[:kh])
  elseif sem == :SPO  Span(maps[:oc], maps[:od])
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
function can_match(r::Rule{T}, m; initial=Dict(),
                   seen=Set()) where T

  for (k,v) in pairs(components(m))
    if has_comp(r.monic,k) && !is_monic(v)
      return ("Match is not injective", k, v)
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
    tri = extend_morphism(m, N.f;  monic=N.monic, init_check=N.init_check)
    if isnothing(tri) == N.positive
      return ("$(pos(N))AC failed", nᵢ, isnothing(tri) ? () : components(tri))
    end
  end

  if !isempty(seen)
    res = rewrite_match(r, m; kw...)
    for s in seen
      if is_isomorphic(s,res)
        return ("Result is iso to previously seen result", s)
      end
    end
  end

  return nothing
end

"""Get list of possible matches based on the constraints of the rule"""
function get_matches(r::Rule{T}, G; initial=nothing, seen=Set(),
                     verbose=false) where T
  initial = isnothing(initial) ? Dict() : initial
  hs = homomorphisms(codom(r.L), G; monic=r.monic,
                     initial=NamedTuple(initial))
  collect(filter(hs) do h
    cm = can_match(r,h)
    if verbose && !isnothing(cm)
      println("$([k => collect(v) for (k,v) in pairs(components(h))]): $cm")
    end
    isnothing(cm)
  end)
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
function get_expr_binding_map(r::Rule{T}, m, result) where T
  X = codom(result)
  comps = Dict(map(attrtypes(acset_schema(X))) do at 
      bound_vars = Vector{Any}(collect(m[at]))
      binding = Any[nothing for _ in 1:nparts(X, at)]
      for (v, expr) in zip(freevars(r, at), r.exprs[at])
        binding[result[at](v)] = subexpr(expr, bound_vars)
      end
      at => binding
  end)
  return sub_vars(X, comps)
end
get_expr_binding_map(::PBPORule, _, result) = result
get_expr_binding_map(::AttrPBPORule, _, result) = result


"""Replace AttrVars with values"""
function subexpr(expr::Expr, bound_vars::Vector{Any})
  x = deepcopy(expr)
  for (i, v) in enumerate(bound_vars)
    rep!(x, Expr(:call, :AttrVar, i), v)
  end
  return eval(x)
end

"""Replace old with new in an expression recursively"""
function rep!(e, old, new)
  for (i,a) in enumerate(e.args)
    if a==old
      e.args[i] = new
    elseif a isa Expr
      rep!(a, old, new)
    end # otherwise do nothing
  end
  e
end



# Rewriting functions that just get the final result
####################################################

function rewrite_match_maps end  # to be implemented for each T

"""    rewrite(r::Rule, G; kw...)
Perform a rewrite (automatically finding an arbitrary match) and return result.
"""
function rewrite(r::AbsRule, G; kw...)
  ms = get_matches(r, G)
  return isempty(ms) ? nothing : rewrite_match(r, first(ms); kw...)
end


"""    rewrite_match(r::Rule, m; kw...)
Perform a rewrite (with a supplied match morphism) and return result.
"""
rewrite_match(r::AbsRule, m; kw...) =
  codom(get_expr_binding_map(r, m, get_rmap(ruletype(r), 
                                            rewrite_match_maps(r,m; kw...))))

  """    rewrite_parallel(rs::Vector{Rule}, G; kw...)
  Perform multiple rewrites in parallel (automatically finding arbitrary matches)
  and return result.
  """
rewrite_parallel(rs::Vector{Rule{T}}, G; kw...) where {T} =
    get_result(T, rewrite_parallel_maps(rs, G; kw...))

rewrite_parallel(r::Rule, G; kw...) = rewrite_parallel([r], G; kw...)

# Rewriting function which return the maps, too
###############################################
"""    rewrite_full_output(r::Rule, G; initial=Dict(), kw...)
Perform a rewrite (automatically finding an arbitrary match) and return a tuple:
1.) the match morphism 2.) all computed data 3.) variable binding morphism
"""
function rewrite_full_output(r::AbsRule, G; initial=nothing, random=false,
                            seen=Set(), verbose=false, kw...) 
  T = ruletype(r)
  ms = get_matches(r,G,initial=initial, seen=seen, verbose=verbose)
  if isempty(ms)
    return nothing
  elseif random
    shuffle!(ms)
  end
  m = first(ms)
  rdata = rewrite_match_maps(r, m; verbose=verbose, kw...)
  return (m, rdata, codom(get_expr_binding_map(r, m, get_rmap(T, rdata))))
end

# Executing multiple rewrites
#############################

"""
Take a graph G and a rewrite rule and look for all possible matches.
Execute the sequence in random or an arbitrary (but deterministic) order.
"""
function rewrite_sequential_maps(r::Rule{T}, G; random=false, seen=Set(),
                                 verbose=verbose, prob=1.0, kw...) where {T}
  ms = get_matches(r,G; seen=seen, verbose=verbose)
  output = Any[(create(G), Span(id(G), id(G)), G)]
  if isempty(ms)
    return Any[]
  elseif random
    shuffle!(ms)
  end

  for m in ms
    _, prev_span, _ = output[end]
    m′ = postcompose_partial(prev_span, m)
    if !isnothing(m′) && is_natural(m′)
      if isnothing(can_match(r′, m′)) && rand() < prob
        res = rewrite_match_maps(r′, m′; kw...)
        prev_span = get_pmap(T, res)
        push!(output, (m′, get_pmap(T, res), get_result(T, res)))
      end
    end
  end
  output[2:end]
end

"""    rewrite_parallel_maps(rs::Vector{Rule{T}}, G::StructACSet{S}; initial=Dict(), kw...) where {S,T}
Perform multiple rewrites in parallel (automatically finding arbitrary matches)
and return all computed data. Restricted to C-set rewriting
"""
function rewrite_parallel_maps(rs::Vector{Rule{T}}, G::StructACSet{S};
                               initial=Dict(), kw...) where {S,T}

    (ms,Ls,Rs) = [ACSetTransformation{S}[] for _ in 1:3]
    seen = [Set{Int}() for _ in ob(S)]
    init = NamedTuple(initial) # UNUSED
    for r in rs
      ms = get_matches(r,G,initial=initial, seen=seen)
      for m in ms
        new_dels = map(zip(components(r.L), components(m))) do (l_comp, m_comp)
          L_image = Set(collect(l_comp))
          del = Set([m_comp(x) for x in codom(l_comp) if x ∉ L_image])
          LM_image = Set(m_comp(collect(L_image)))
          return del => LM_image
        end
        if all(isempty.([x∩new_keep for (x,(_, new_keep)) in zip(seen, new_dels)]))
          for (x, (new_del, new_keep)) in zip(seen, new_dels)
            union!(x, union(new_del, new_keep))
          end
          push!(ms, m); push!(Ls, deepcopy(r.L)); push!(Rs, r.R)
        end
      end
    end

  if isempty(ms) return nothing end
  length(Ls) == length(ms) || error("Ls $Ls")

  # Composite rewrite rule
  R = Rule{T}(oplus(Ls), oplus(Rs))

  return rewrite_match_maps(R, copair(ms); kw...)
end

rewrite_parallel_maps(r::Rule, G; initial=Dict(), kw...) =
  rewrite_parallel_maps([r], G; initial=initial, kw...)

end # module
