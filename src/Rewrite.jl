module Rewrite

export Rule, PAC, NAC, rewrite, rewrite_match, rewrite_parallel,
       rewrite_match_maps, rewrite_parallel_maps, rewrite_dpo, rewrite_spo,
       rewrite_sqpo, final_pullback_complement, pullback_complement, get_result,
       get_pmap, get_rmap, rewrite_sequential_maps, ruletype

using Catlab, Catlab.Theories, Catlab.Schemas
using Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.FinSets: IdentityFunction
using Catlab.CategoricalAlgebra.CSets: type_components
using Catlab.CategoricalAlgebra.DataMigrations: MigrationFunctor
import Catlab.Theories: dom, codom
import Catlab.CategoricalAlgebra: is_natural,components
using StructEquality
using Random
using Catlab.ColumnImplementations: AttrVar

using ..CSets, ..PartialMap

# Application conditions
###########################
"""
Application conditions, either positive or negative.

This can be attached to a rule as a morphism f: L->AC. When a match morphism is 
found, we are concerned with triangles:
 AC <-- L <-- I --> R
    ↘  ↓
      G
  
If the condition is positive, we demand that the triangle commutes for the match 
to be considered valid. If it is negative, we forbid such a triangle.

An important subtlety is that monicity is only checked during AC evaluation
for the elements that are *not* assigned in virtue of the match morphism. Here
is an example:

L is a single vertex but we want to match vertices with at most one inneighbor.
AC has (a cospan shape), since the two inneighbors might be
different (therefore, the match constraint is not monic).
"""
struct AppCond
  f::ACSetTransformation
  positive::Bool
  monic::Union{Bool, Vector{Symbol}}
  init_check::Bool
  AppCond(f::ACSetTransformation, p=false, m=false, init_check=true) = 
    new(f, p, m, init_check)
end

AppCond(nac::AppCond) = nac
pos(nac::AppCond) = nac.positive ? "Positive" : "Negative"
NAC(f::ACSetTransformation, m=false, init_check=true) = AppCond(f,false,m,init_check)
PAC(f::ACSetTransformation, m=false, init_check=true) = AppCond(f,true,m,init_check)
codom(n::AppCond) = codom(n.f)
dom(n::AppCond) = dom(n.f)
is_natural(n::AppCond) = is_natural(n.f)
components(n::AppCond) = components(n.f)
(F::DeltaMigration)(n::AppCond) = AppCond(F(n.f), n.positive, n.monic, n.init_check)

# Check if a component is included in a monic constraint
has_comp(monic::Bool, c::Symbol) = monic
has_comp(monic::Vector{Symbol}, c::Symbol) = c ∈ monic

# RULES 
#######

"""
Rewrite rules which are encoded as spans. 
The L structure encodes a pattern to be matched. 
The R morphism encodes a replacement pattern to be substituted in.
They are related to each other by an interface I with maps: L ⟵ I ⟶ R 

A semantics (DPO, SPO, or SqPO) must be chosen.

Control the match-finding process by specifying whether the match is
intended to be monic or not, as well as an optional application
condition(s) 

Monic constraints can be independently given
to the match morphism and to the morphisms searched for when checking NAC.
"""
struct Rule{T}
  L::Any
  R::Any
  conditions::Vector{AppCond}
  monic::Union{Bool, Vector{Symbol}}
  exprs::Dict{Symbol, Vector{Expr}}
  function Rule{T}(L, R; ac=nothing, monic=false, expr=nothing) where {T}
    dom(L) == dom(R) || error("L<->R not a span")
    ACs = Vector{AppCond}(isnothing(ac) ? [] : (ac isa AbstractVector ? ac : [NAC(ac)]))
    exprs = isnothing(expr) ? Dict() : expr
    all(N-> dom(N) == codom(L), ACs) || error("AppCond does not compose with L $(codom(L))")
    map(enumerate([L,R,ACs...])) do (i, f)
      if !is_natural(f)
        show(stdout, "text/plain",dom(f))
        show(stdout, "text/plain",codom(f))
        println("cs(f) $(components(f)) \ntype_cs $(type_components(f))")
        error("unnatural map #$i: $f")
      end
    end
    for (o, xs) in collect(exprs)
      n = nparts(codom(R),o) - nparts(dom(R), o)
      n == length(xs) || error("$n exprs needed for part $o")
    end 
    new{T}(L, R, ACs, monic, exprs)
  end
end

Rule(l,r;kw...) = Rule{:DPO}(l,r; kw...)

ruletype(::Rule{T}) where T = T


(F::DeltaMigration)(r::Rule{T}) where {T} =
  Rule{T}(F(r.L), F(r.R), F.(r.conditions); monic=r.monic)



# Rewriting functions that just get the final result
####################################################
"""    rewrite(r::Rule, G; kw...)
Perform a rewrite (automatically finding an arbitrary match) and return result.
"""
function rewrite(r::Rule{T}, G; kw...) where {T}
  ms = get_matches(r, G)
  return isempty(ms) ? nothing : rewrite_match(r, first(ms); kw...)
end


"""    rewrite_match(r::Rule, m; kw...)
Perform a rewrite (with a supplied match morphism) and return result.
"""
rewrite_match(r::Rule{T}, m; kw...) where {T} =
  codom(get_expr_binding_map(r, m, get_rmap(T, rewrite_match_maps(r,m; kw...))))

"""    rewrite_parallel(rs::Vector{Rule}, G; kw...)
Perform multiple rewrites in parallel (automatically finding arbitrary matches)
and return result.
"""
rewrite_parallel(rs::Vector{Rule{T}}, G; kw...) where {T} =
  get_result(T, rewrite_parallel_maps(rs, G; kw...))
rewrite_parallel(r::Rule, G; kw...) = rewrite_parallel([r], G; kw...)


"""Extract the map from the R to the result from the full output data"""
function get_rmap(sem::Symbol, maps)
  if isnothing(maps)  nothing
  elseif sem == :DPO  maps[3]
  elseif sem == :SPO  Span(maps[7], maps[8]) # UNSTABLE: a partial map 
  elseif sem == :SqPO maps[1]
  else   error("Rewriting semantics $sem not supported")
  end
end

function get_result(sem::Symbol, maps)
  if isnothing(maps)  nothing
  elseif sem == :DPO  codom(maps[4])
  elseif sem == :SPO  codom(maps[8])
  elseif sem == :SqPO codom(maps[1])
  else   error("Rewriting semantics $sem not supported")
  end
end

"""Extract the partial map (derived rule) from full output data"""
function get_pmap(sem::Symbol, maps)
  if isnothing(maps)  nothing
  elseif sem == :DPO  Span(maps[2], maps[4])
  elseif sem == :SPO  Span(maps[6], maps[8])
  elseif sem == :SqPO Span(maps[4], maps[2])
  else   error("Rewriting semantics $sem not supported")
  end
end

# Match finding
################
check_initial(vs::Vector{Int}, f::Vector{Int}) =
  [(i, vs[i], f[i]) for i in length(f) if vs[i]!=f[i]]
check_initial(vs::Vector{Pair{Int,Int}}, f::Vector{Int}) =
  [(i,f[i],v) for (i,v) in vs if f[i]!=v]


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
function get_matches(r::Rule{T}, G; initial=Dict(), seen=Set(),
                     verbose=false) where T
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

# Rewriting function which return the maps, too
###############################################
"""    rewrite_maps(r::Rule, G; initial=Dict(), kw...)
Perform a rewrite (automatically finding an arbitrary match) and return a pair:
the match morphism + all computed data.
"""
function rewrite_with_match(r::Rule{T}, G; initial=Dict(), random=false,
                            seen=Set(),kw...) where {T}
  ms = get_matches(r,G,initial=initial, seen=seen)
  if isempty(ms)
    return nothing
  elseif random
    shuffle!(ms)
  end
  m = first(ms)
  return m => rewrite_match_maps(r, m; kw...)
end

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
    init = NamedTuple(initial)
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

# Double-pushout rewriting
##########################

"""    rewrite_match_maps(r::Rule{:DPO}, m)
Apply a DPO rewrite rule (given as a span, L<-I->R) to a ACSet
using a match morphism `m` which indicates where to apply
the rewrite.
              l   r
           L <- I -> R
         m ↓    ↓    ↓
           G <- K -> H

This works for any type that implements `pushout_complement` and `pushout`

Returns the morphisms I->K, K->G (produced by pushout complement), followed by
R->H, and K->H (produced by pushout)
"""
function rewrite_match_maps(r::Rule{:DPO}, m; check::Bool=false)
  if check
    err = "Cannot pushout complement $r\n$m"
    can_pushout_complement(ComposablePair(r.L, m)) || error(err)
  end
  ik, kg = pushout_complement(ComposablePair(r.L, m))  
  rh, kh = pushout(r.R, ik) 
  return ik, kg, rh, kh
end


# Sesqui-pushout rewriting
##########################

"""
The specification for the following functions comes from:
  - 'Concurrency Theorems for Non-linear Rewriting Theories'
     - for final pullback complement and sesqui-pushout rewriting
  - 'AGREE - Algebraic Graph Rewriting with Controlled Embedding'
     - for partial map classifier (a functor T and natural transformation η)

This implementation is specialized to rewriting CSets
"""

"""
See Theorem 2 of 'Concurrency Theorems for Non-linear Rewriting Theories'
      f
  B <--- A
m ↓      ↓ n
  C <--  D
     g

"""
function final_pullback_complement(fm::ComposablePair;
    pres::Union{Nothing, Presentation}=nothing, check=false)::ComposablePair
  f, m = fm
  A, B = dom(f), codom(f)
  m_bar = partial_map_classifier_universal_property(m, id(B); pres=pres)
  T_f = partial_map_functor_hom(f; pres=pres)
  pb_2 = pullback(T_f, m_bar)
  _, g = pb_2.cone
  s = Span(partial_map_classifier_eta(A; pres=pres), compose(f,m))
  n = universal(pb_2, s)
  !check || is_isomorphic(apex(pullback(m,g)), A) || error("incorrect")
  return ComposablePair(n, g)
end

"""    rewrite_match_maps(r::Rule{:SqPO},m; pres::Union{Nothing, Presentation}=nothing)
Sesqui-pushout is just like DPO, except we use a final pullback complement
instead of a pushout complement.
"""
function rewrite_match_maps(r::Rule{:SqPO},m; pres::Union{Nothing, Presentation}=nothing)
  m_, i_ = final_pullback_complement(ComposablePair(r.L, m); pres=pres)
  m__, o_ = pushout(r.R, m_)
  return (m__, o_, m_, i_)
end


# Single-pushout rewriting
##########################

"""
  f         f
A ↣ B     A ↣ B
    ↓ g   ↓   ↓ g
    C     D ↣ C

Pullback complement where there first morphism is a mono.

Define D to be Im(g) to make it the largest possible subset of C such that we
can get a pullback.
"""
function pullback_complement(f, g)
  is_monic(f) || error("can only take pullback complement if f is mono")
  A = dom(f)
  d_to_c = hom(¬g(¬f(A))) # why isn't this just g(B)?
  # force square to commute by looking for the index in D making it commute
  ad = Dict(map(collect(pairs(components(compose(f,g))))) do (cmp, fg_as)
    cmp => Vector{Int}(map(collect(fg_as)) do fg_a
      findfirst(==(fg_a), collect(d_to_c[cmp]))
    end)
  end)
  return CSetTransformation(A, dom(d_to_c); ad...) => d_to_c
end

"""    rewrite_match_maps(r::Rule{:SPO}, ac)
NOTE: In the following diagram, a double arrow indicates a monic arrow.

We start with two partial morphisms, construct M by pullback, then N & O by
pullback complement, then finally D by pushout.


A ⇇ K → B         A ⇇ K → B
⇈                 ⇈ ⌟ ⇈ ⌞ ⇈
L          ⭆      L ⇇ M → N
↓                 ↓ ⌞ ↓ ⌜ ↓
C                 C ⇇ O → D

We assume the input A→C is total, whereas A→B may be partial, so it is given
as a monic K↣A and K→B.

Specified in Fig 6 of:
"Graph rewriting in some categories of partial morphisms"
"""
function rewrite_match_maps(r::Rule{:SPO}, ac)
  ka, kb = r.L, r.R
  e = "SPO rule is not a partial morphism. Left leg not monic."
  is_monic(ka) || error(e)

  lc, la = ac, id(dom(ac))
  ml, mk = pullback(la, ka)
  mn, nb = pullback_complement(mk, kb)
  mo, oc = pullback_complement(ml, lc)
  od, nd = pushout(mo, mn)
  return [ml, mk, mn, mo, nb, oc, nd, od]
end

end # module
