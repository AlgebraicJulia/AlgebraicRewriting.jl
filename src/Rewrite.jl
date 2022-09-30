module Rewrite

export Rule, NAC, rewrite, rewrite_match, rewrite_parallel,
       rewrite_match_maps, rewrite_parallel_maps, rewrite_dpo, rewrite_spo,
       rewrite_sqpo, final_pullback_complement, pullback_complement, get_result,
       get_pmap, rewrite_sequential_maps

using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra: DeltaMigration, CSetTransformation, TightACSetTransformation, ACSetTransformation, LooseACSetTransformation, pullback, pushout,  StructACSet, ComposablePair, copair, Span, universal, ¬, ob_map
using Catlab.CategoricalAlgebra.CSets: type_components
using Catlab.CategoricalAlgebra.DataMigrations: MigrationFunctor
import Catlab.Theories: dom, codom
import Catlab.CategoricalAlgebra: is_natural,components
using AutoHashEquals
using Random

using ..Variables, ..CSets, ..PartialMap, ..Search
import ..Variables: sub_vars

# Generic rewriting tooling
###########################
struct NAC
  f::ACSetTransformation
  monic::Union{Bool, Vector{Symbol}}
  init_check::Bool
end

NAC(f::ACSetTransformation, m=false, init_check=true) = NAC(f, m, init_check)
NAC(nac::NAC) = nac
codom(n::NAC) = codom(n.f)
dom(n::NAC) = dom(n.f)
is_natural(n::NAC) = is_natural(n.f)
sub_vars(nac::NAC, m) = NAC(sub_vars(nac.f, m), nac.monic)
components(n::NAC) = components(n.f)

has_comp(monic::Bool, c::Symbol) = monic
has_comp(monic::Vector{Symbol}, c::Symbol) = c ∈ monic

"""
Rewrite rules are encoded as spans. The L morphism encodes a pattern to be
matched. The R morphism encodes a replacement pattern to be substituted in.

A semantics (DPO, SPO, or SqPO) must be chosen.

Control the match-finding process by specifying whether the match is
intended to be monic or not, as well as an optional negative application
condition(s) (i.e. forbid any match m: L->G for which there exists a commuting
triangle L->Nᵢ->G, for each Nᵢ). Monic constraints can be independently given
to the match morphism and to the morphisms searched for when checking NAC.

An important subtlety is that monicity is only checked during NAC evaluation
for the elements that are not assigned in virtue of the match morphism. Here
is an example:

We want to rewrite vertices with exactly two inneighbors.
L has three vertices (a cospan shape), since the two inneighbors might be
different (therefore, the match constraint is not monic).

"""
struct Rule{T}
  L::Any
  R::Any
  N::Vector{NAC}
  monic::Union{Bool, Vector{Symbol}}
  function Rule{T}(L, R, N=nothing; monic=false) where {T}
    dom(L) == dom(R) || error("L<->R not a span")
    Ns = isnothing(N) ? NAC[] : (N isa AbstractVector ? NAC.(N) : [NAC(N)])
    all(N-> dom(N) == codom(L), Ns) || error("NAC does not compose with L")
    map(enumerate([L,R,Ns...])) do (i, f)
      if !is_natural(f)
        println(stdout, "text/plain",dom(f))
        println(stdout, "text/plain",codom(f))
        error("unnatural map #$i: $f")
      end
    end
    new{T}(L, R, Ns, monic)
  end
end
Rule(L,R,N=nothing;monic=false) = Rule{:DPO}(L,R,N; monic=monic)

# THIS SHOULD BE UPSTREAMED TO CATLAB
(F::DeltaMigration{T})(f::TightACSetTransformation{S}) where {T,S} = begin
  F isa DeltaMigration || error("Only Δ migrations supported on morphisms")
  d = Dict(map(collect(pairs(components(f)))) do (k,v)
    Symbol(ob_map(F.functor,k)) => v
  end)
  TightACSetTransformation(NamedTuple(d), F(dom(f)), F(codom(f)))
end

"""Need to do the swapping of type components too"""
(F::DeltaMigration{T})(f::LooseACSetTransformation{S}) where {T,S} = begin
  F isa DeltaMigration || error("Only Δ migrations supported on morphisms")
  d = Dict(map(collect(pairs(components(f)))) do (k,v)
    Symbol(ob_map(F.functor,k)) => v
  end)
  td = Dict(map(collect(pairs(type_components(f)))) do (k,v)
    Symbol(ob_map(F.functor,k)) => v
  end)

  LooseACSetTransformation(NamedTuple(d),NamedTuple(td),F(dom(f)), F(codom(f)))
end


(F::DeltaMigration)(n::NAC) = NAC(F(n.f), n.monic, n.init_check)

(F::DeltaMigration)(r::Rule{T}) where {T} =
  Rule{T}(F(r.L), F(r.R), F.(r.N); monic=r.monic)

"""
Negative application conditions that are rendered unnatural by substitution
are inactive. E.g. an edge weight is a variable in L but set to 0 in the NAC.
When a nonzero edge is matched, this NAC becomes unnatural.
"""
function sub_vars(R::Rule, m::LooseACSetTransformation)
  Ns = filter(is_natural, [sub_vars(N, m) for N in R.N])
  Rule(sub_vars(R.L, m), sub_vars(R.R, m), Ns, monic=R.monic)
end


# Rewriting functions that just get the final result
####################################################
"""    rewrite(r::Rule, G; kw...)
Perform a rewrite (automatically finding an arbitrary match) and return result.
"""
function rewrite(r::Rule{T}, G; kw...) where {T}
  match_res = rewrite_with_match(r, G; kw...)
  isnothing(match_res) ? nothing : get_result(T, match_res[2])
end


"""    rewrite_match(r::Rule, m; kw...)
Perform a rewrite (with a supplied match morphism) and return result.
"""
rewrite_match(r::Rule{T}, m; kw...) where {T} =
  get_result(T, rewrite_match_maps(r, m; kw...))

"""    rewrite_parallel(rs::Vector{Rule}, G; kw...)
Perform multiple rewrites in parallel (automatically finding arbitrary matches)
and return result.
"""
rewrite_parallel(rs::Vector{Rule{T}}, G; kw...) where {T} =
  get_result(T, rewrite_parallel_maps(rs, G; kw...))
rewrite_parallel(r::Rule, G; kw...) = rewrite_parallel([r], G; kw...)


"""Extract the rewrite result from the full output data"""
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

instantiate(r,m) = hasvar(codom(r.L)) ? (sub_vars(r,m), sub_vars(m,m)) : (r,m)


"""
Returns nothing if the match is acceptable for rewriting according to the
rule, otherwise returns the reason why it should be rejected
"""
function can_match(r::Rule{T}, m; initial=Dict(),
                   seen=Set()) where T
  for (k,v) in pairs(components(m))
    if has_comp(r.monic,k) && !is_injective(v)
      return ("Match is not injective", k, v)
    end
  end
  for (k, vs) in collect(initial)
    errs = check_initial(vs, collect(m[k]))
    if !isempty(errs)
      return ("Initial condition violated",k, errs)
    end
  end

  r′ ,m′ = instantiate(r, m)

  if T == :DPO
    gc = gluing_conditions(ComposablePair(r′.L, m′))
    if !isempty(gc)
      return ("Gluing conditions failed", gc)
    end
  end

  for (nᵢ, N) in enumerate(r′.N)
    tri = extend_morphism(m′, N.f;  monic=N.monic, init_check=N.init_check)
    if !isnothing(tri)
      return ("NAC failed", nᵢ, components(tri))
    end
  end

  if !isempty(seen)
    res = rewrite_match(r′, m′; kw...)
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
  hs = homomorphisms(codom(r.L), G; bindvars=true, monic=r.monic,
                     initial=NamedTuple(initial))
  collect(filter(hs) do h
    cm = can_match(r,h)
    if verbose && !isnothing(cm)
      println("$([k => collect(v) for (k,v) in pairs(components(h))]): $cm")
    end
    isnothing(cm)
  end)
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
  r′ ,m′ = instantiate(r, first(ms))
  return m′ => rewrite_match_maps(r′, m′; kw...)
end

"""
Convert a match L->G to a match L->H using a partial morphism G->H, if possible.
       L ========= L
     m ↓           ↓ m'
       G <-- K --> H

This ought be written more generically so that it can work with, e.g., slices.
"""
function postcompose_partial(kgh::Span, m::ACSetTransformation)
  d = Dict()
  kg, kh = kgh
  for (k,vs) in pairs(components(m))
    vs_ = Int[]
    for v in collect(vs)
      kv = findfirst(==(v), collect(kg[k]))
      if isnothing(kv)
        mc = nothing
        return nothing
      else
        push!(vs_, kh[k](kv))
      end
    end
    d[k] = vs_
  end
  ACSetTransformation(dom(m), codom(kh); d...)
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
    r′, m′= instantiate(r, m)
    m′′ = postcompose_partial(prev_span, m′)
    if !isnothing(m′′) && is_natural(m′′)
      if isnothing(can_match(r′, m′′)) && rand() < prob
        res = rewrite_match_maps(r′, m′′; kw...)
        prev_span = get_pmap(T, res)
        push!(output, (m′′, get_pmap(T, res), get_result(T, res)))
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
    can_pushout_complement(ComposablePair(r.L, m)) || error("Cannot pushout complement $r\n$m")
  end
  (ik, kg) = pushout_complement(ComposablePair(r.L, m))
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
  is_injective(f) || error("can only take pullback complement if f is mono")
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
  is_injective(ka) || error(e)

  lc, la = ac, id(dom(ac))
  ml, mk = pullback(la, ka)
  mn, nb = pullback_complement(mk, kb)
  mo, oc = pullback_complement(ml, lc)
  od, nd = pushout(mo, mn)
  return [ml, mk, mn, mo, nb, oc, nd, od]
end

end # module
