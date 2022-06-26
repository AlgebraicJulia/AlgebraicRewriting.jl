module Rewrite

export Rule, rewrite, rewrite_match, rewrite_parallel, rewrite_maps,
       rewrite_match_maps, rewrite_parallel_maps, rewrite_dpo, rewrite_spo,
       rewrite_sqpo, final_pullback_complement, pullback_complement

using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra: CSetTransformation, ACSetTransformation, LooseACSetTransformation, pullback, pushout, components, StructACSet, ComposablePair, is_natural, copair, Span, universal, ¬
using AutoHashEquals
using Random

using ..Variables, ..CSets, ..PartialMap, ..Search
import ..Variables: sub_vars

# Generic rewriting tooling
###########################
"""
Rewrite rules are encoded as spans. The L morphism encodes a pattern to be
matched. The R morphism encodes a replacement pattern to be substituted in.

A semantics (DPO, SPO, or SqPO) must be chosen.

Control the match-finding process by specifying whether the match is
intended to be monic or not, as well as an optional negative application
condition(s) (i.e. forbid any match m: L->G for which there exists a commuting
triangle L->Nᵢ->G, for each Nᵢ).
"""
struct Rule{T}
  L::Any
  R::Any
  N::Vector{Any}
  monic::Bool
  function Rule{T}(L, R, N=nothing; monic::Bool=false) where {T}
    dom(L) == dom(R) || error("L<->R not a span")
    Ns = isnothing(N) ? [] : (N isa ACSetTransformation ? Any[N] : N)
    all(N-> dom(N) == codom(L), Ns) || error("NAC does not compose with L")
    new{T}(L, R, Ns, monic)
  end
end
Rule(L,R,N=nothing;monic::Bool=false) = Rule{:DPO}(L,R,N; monic=monic)


function sub_vars(R::Rule, m::LooseACSetTransformation)
  Rule(sub_vars(R.L, m), sub_vars(R.R, m),
     [sub_vars(N, m) for N in R.N], monic=R.monic)
end


# Rewriting functions that just get the final result
####################################################
"""    rewrite(r::Rule, G; kw...)
Perform a rewrite (automatically finding an arbitrary match) and return result.
"""
rewrite(r::Rule{T}, G; kw...) where {T} =
  let res = rewrite_maps(r, G; kw...);
  isnothing(res) ? nothing : get_result(T, res[2]) end

function rewrite_with_match(r::Rule{T}, G; kw...) where {T}
  r = rewrite_maps(r, G; kw...);
  if isnothing(r) return nothing end
  get_result(T, r[2]) => r[1]
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

# Rewriting function which return the maps, too
###############################################
"""    rewrite_maps(r::Rule, G; initial=Dict(), kw...)
Perform a rewrite (automatically finding an arbitrary match) and return a pair:
the match morphism + all computed data.
"""
function rewrite_maps(r::Rule{T}, G; initial=Dict(), random=false, seen=Set(),
                      kw...) where {T}
  ms = homomorphisms(codom(r.L), G; monic=r.monic, initial=NamedTuple(initial))
  if random
    shuffle!(ms)
  end
  for m in ms
    var = hasvar(codom(r.L))
    r′ ,m′ = var ? (sub_vars(r, m), sub_vars(m, m)) : (r, m)
    if !all(is_natural, r.N)
      error("unnatural $(components.(r.N))")
      continue
    end
    DPO_pass = T != :DPO || can_pushout_complement(ComposablePair(r′.L, m′))

    if DPO_pass && all(N->isnothing(extend_morphism(m′, N; monic=true)), r′.N)
      res = rewrite_match_maps(r′, m′; kw...)
      if all(s->!is_isomorphic(s,get_result(T,res)), seen)
        return m => res
      end
    end
  end
  return nothing
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
    ms_ = homomorphisms(codom(r.L), G; monic=r.monic, initial=init)
    for m in ms_
      DPO_pass = T != :DPO || can_pushout_complement(ComposablePair(r.L, m))
      if DPO_pass && all(N->isnothing(extend_morphism(m,N)), r.N)
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
    A = dom(f)
    d_to_c = hom(¬g(¬f(A)))
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