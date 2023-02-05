module PBPO 
export PBPORule

import ..Utils: 
  rewrite_match_maps, get_matches, get_expr_binding_map, AbsRule, ruletype
using ..Utils
using ..Constraints
using ...CategoricalAlgebra

using ...CategoricalAlgebra.CSets: 
  extend_morphisms, abstract, var_pullback, remove_freevars
using Catlab, Catlab.CategoricalAlgebra
import Catlab.CategoricalAlgebra: left, right
using StructEquality

"""
      l    r 
   L  ⟵ K ⟶ R 
tl ↓     ↓ tk     <== these must be monic
   L' ⟵ K'

It is assumed we never want the typing/adherence match to be monic, but we 
can optionally restrict the match L → G to be monic.

We can attach application conditions to both the match morphism as well as the 
adherence morphism. 
"""
@struct_hash_equal struct PBPORule <: AbsRule
  l
  r
  tl
  tk 
  l′
  monic::Union{Bool, Vector{Symbol}}
  acs::Vector{Constraint}
  lcs::Vector{Constraint}
  exprs::Dict 
  k_exprs::Dict
  function PBPORule(l,r,tl,tk,l′; monic=true, acs=[], lcs=[], 
                    expr=nothing,k_expr=nothing)
    # check things match up
    S = acset_schema(dom(l))
    all(is_natural, [l,r,tl,tk,l′]) || error("Unnatural")
    dom(l) == dom(r) == dom(tk) || error("bad K")
    codom(l) == dom(tl) || error("bad L")
    codom(tk) == dom(l′) || error("bad K'")
    codom(l′) == codom(tl) || error("bad L'")
    check_pb(deattr.([tl,l′,l,tk])...) || error("(l,tk) not the pullback of (tl,l′)")
    all(o->is_monic(tl[o]), ob(S)) || error("tl map must be monic $tl")
    all(o->is_monic(tk[o]), ob(S)) || error("tk map must be monic $tk")
    # check adherence conditions?
    exprs = isnothing(expr) ? Dict() : Dict(pairs(expr))
    k_exprs = isnothing(k_expr) ? Dict() : Dict(pairs(k_expr))

    return new(l,r,tl,tk,l′, monic, acs, lcs, exprs, k_exprs)
  end
end

ruletype(::PBPORule) = :PBPO
left(r::PBPORule) = r.l 
right(r::PBPORule) = r.r

(F::Migrate)(r::PBPORule) =
  PBPORule(F(r.l), F(r.r), F(r.tl), F(r.tk), F(r.l′); monic=r.monic,
           acs=F.(r.acs), lcs=F.(r.lcs), expr=F(r.exprs), k_expr=F(r.k_exprs))


"""
Take a PBPO rule and put into normal form, i.e. 
where the lower square forms a pullback

See Prop 2.4 of "The PBPO graph transformation approach"
"""
function canon(l,r,tl,tk,l′)::PBPORule
  new_l , new_tk = pb = pullback(tl, l′)
  ns = filter(n->force(n⋅new_tk)==force(tk), 
              homomorphisms(dom(l), apex(pb)))
  n = only(ns) # is there a better way to get this via pullback?
  new_r, _ = pushout(n, r)
  PBPORule(force.([new_l, new_r, tl, new_tk,l′])...)
end

"""
PBPO matches consist of *two* morphisms. First, a match L → G and secondly 
a typing G → L′. 

We enumerate matches first and then consider, for each of them, if there is a 
valid typing.
     m
  L⌟ ⟶ G 
  ||    ↓ α
  L  ⟶ L′
     tl

     ∀m
   L ⟶ G 
tl ↓ ↘a ↑ (abstraction)
   L′⟵ A 
      α

Search over all pairs m: L->G and α:A->L′. 
"Strong match" condition we check is that: tl⁻¹(α(A)) = a⁻¹(A).
"""
function get_matches(rule::PBPORule, G::StructACSet{S}; verbose=false, 
                     initial=nothing, kw...) where S
  res = []
  if isnothing(initial)
    matchinit, typinit = Dict(), Dict()
  elseif initial isa Union{NamedTuple,AbstractDict}
    matchinit, typinit = Dict(pairs(initial)), Dict()
  elseif length(initial)==2
    matchinit, typinit = [Dict(pairs(x)) for x in initial]
  else 
    error("Unexpected type for `initial` keyword: $initial")
  end 
  L = codom(left(rule))
  for m in homomorphisms(L, G; monic=rule.monic, initial=NamedTuple(matchinit))
    if all(ac->apply_constraint(ac, m), rule.acs)
      if verbose 
        println("m: ", [k=>collect(v) for (k,v) in pairs(components(m))]) 
      end
      # Construct maps a:L->A and ab A->G such that m = a;ab
      ab = abstract(G)
      A = dom(ab)    
      ainit = NamedTuple(Dict(o=>collect(m[o]) for o in ob(S)))
      for (a, cd, _) in attrs(S)
        for (v, fv) in filter(v_->!(v_[2] isa AttrVar),collect(enumerate(L[a])))
          A[m[cd](v), a] = fv
        end
      end 
      ab = remove_freevars(ab)
      A = dom(ab)
      a = only(homomorphisms(L, A; initial=ainit))
      for α in extend_morphisms(rule.tl, a; initial=typinit)
        if verbose 
          println("\tα: ", [k=>collect(v) for (k,v) in pairs(components(α))]) 
        end
        strong_match = all(ob(S)) do o 
          all(parts(A,o)) do i 
            p1 = preimage(rule.tl[o],α[o](i))
            p2 = preimage(a[o], i)
            sort(p1) == sort(p2)
          end
        end
        if strong_match && all(lc -> apply_constraint(lc, α), rule.lcs)
          all(is_natural, [m,a,ab,α]) || error("Unnatural match")
          if verbose print("\tSUCCESS") end 
          push!(res, (m,a,ab,α))
        elseif verbose 
          println("\tFAILURE (strong $strong_match)")
        end
      end
    end
  end
  return res
end

""" 
             r
          K ----> R
    gₗ    u ↓ gᵣ ⌜ ↓ w
Gₗ <---- Gk ----> Gᵣ
α ↓    ⌞ ↓ u'
 L′ <--  K′
     tₗ

For the adherence morphism α to be valid, it must satisfy a condition with 
m, tₗ. This is checked for matches provided by get_matches, so by default 
we do not check it.

  L <--⌞•
m ↓     ↓
  G ⟵ Gk
"""
function rewrite_match_maps(rule::PBPORule,mα; check=false, kw...)
  _, a, _, α = mα 
  S = acset_schema(dom(left(rule)))
  gl, u′ = var_pullback(Cospan(α, rule.l′)) # A <-- Gk --> K'
  abs_K = abstract(dom(left(rule))) # absK -> K 
  u = only(filter(u->force(compose(u,u′))==force(compose(abs_K,rule.tk)), 
                  homomorphisms(dom(abs_K), dom(u′))))
  abs_r = homomorphism(dom(abs_K), codom(right(rule)); 
                       initial=Dict([o=>collect(right(rule)[o]) for o in ob(S)]))
  # We need to move the map absK-->Gk to K-->Gk. Need a map absK --> K
  w, gr = pushout(abs_r, u)

  # relevant morphisms to return: u′, u, gr, w
  return Dict(:gl=>gl, :u′=>u′, :u=>u, :gr=>gr, :w=>w)
end


"""
Use exprs and k_exprs
"""
function get_expr_binding_map(rule::PBPORule, mtch, res) 
  R, X = dom(res[:w]), codom(res[:w])
  K′ = codom(rule.tk)
  (m, _, ab, _) = mtch

  comps = Dict(map(attrtypes(acset_schema(X))) do at 
    bound_vars = Vector{Any}(collect(m[at]))
    G_bound_vars = Vector{Any}(collect(compose(res[:gl][at],ab[at])))
    K_bound_vars = [k isa AttrVar ? k.val : k for k in collect(res[:u′][at])]
    exprs = haskey(rule.k_exprs,at) ? rule.k_exprs[at] : Dict()
    at => map(parts(X, at)) do x 
      p_r = preimage(res[:w][at], AttrVar(x))
      if !isempty(p_r) 
        v = only(p_r)
        if haskey(rule.exprs,at)
          rx = rule.exprs[at]
          rexpr = rx isa AbstractVector ? rx[v] : get(rx, v, nothing)
          if !isnothing(rexpr)
            return rexpr(bound_vars)
          end
        end
      end 
      # Try to get value via Gk
      p_k = only(preimage(res[:gr][at], AttrVar(x)))
      ik = K_bound_vars[p_k]
      k_expr = exprs isa AbstractVector ? exprs[ik] : get(exprs, ik, nothing)
      if isnothing(k_expr)
        return G_bound_vars[p_k]
      else 
        return k_expr(G_bound_vars[p_k], bound_vars)
      end
    end
  end)
  return sub_vars(X, comps)
end



end # module 
