module PBPO 
import ..RewriteUtils: rewrite_match_maps, get_matches

using ..RewriteDataStructures
using ..Constraints
using ...CategoricalAlgebra

using ...CategoricalAlgebra.CSets: extend_morphisms, decombinatorialize


using Catlab.CategoricalAlgebra

"""
PBPO matches consist of *two* morphisms. First, a match L → G and secondly 
a typing G → L′. 

We enumerate matches first and then consider, for each of them, if there is a 
valid typing.
"""
function get_matches(rule::PBPORule, G; verbose=false, initial=nothing, seen=nothing, kw...)
  res = []
  matchinit, typinit = isnothing(initial) ? (Dict()=>Dict()) : initial 
  L = codom(left(rule))
  for m in homomorphisms(L, G; monic=rule.monic, initial=NamedTuple(matchinit))
    if verbose println("m: ", collect(pairs(components(m)))...) end
    if all(ac->apply_constraint(ac, m), rule.acs)
      alpha_candidates = extend_morphisms(rule.tl, m; initial=typinit)
      if verbose println("length(alpha_candidates) $(length(alpha_candidates))") end
      αs = collect(filter(a->check_pb(rule.tl, a, id(L), m; verbose=verbose) 
                          && all(lc->apply_constraint(lc, a), rule.lcs),
                          alpha_candidates))
      append!(res, [m=>α for α in αs])
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
"""
function rewrite_match_maps(rule::PBPORule,mα; check=false, kw...)
  m, α = mα 
  !check || check_pb(rule.tl, α, id(codom(left(rule))), m) || error("Invalid PBPO match") 

  gl, u′ = pullback(α, rule.l′)
  l_check, u = pullback(m, gl)
  force(l_check) == force(left(rule)) || error("failed l check")
  w, gr = pushout(rule.r, u)

  # relevant morphisms to return: u′, u, gr, w
  return Dict(:gl=>gl, :u′=>u′, :u=>u, :gr=>gr, :w=>w)
end


function get_matches(rule::AttrPBPORule, G::StructACSet; verbose=false, initial=nothing, seen=nothing, kw...)
  G_combo, _ = combinatorialize(G)
  get_matches(rule.combo_rule, G_combo; initial=initial, verbose=verbose, seen=seen)
end

"""
We must pass in the original graph to be rewritten.
"""
function rewrite_match_maps(r::AttrPBPORule, m; G=nothing, kw...) 
  S = acset_schema(dom(r.l))
  _, G_dict = combinatorialize(G)
  res_data = rewrite_match_maps(r.combo_rule, m; kw...)
  combo_res = codom(res_data[:w])
  var_repl = Dict(map(attrtypes(S)) do at 
    bound_vars = [G_dict[at][x] for x in collect(m[1][at])]
    at => map(parts(combo_res, at)) do result_var
      r_var = preimage(res_data[:w][at], result_var)
      if !isempty(r_var) 
        return subexpr(r.exprs[at][only(r_var)], bound_vars)
      else 

        gk_var = preimage(res_data[:gr][at], result_var)
        gl_val = G_dict[at][res_data[:gl][at](gk_var[1])] # G has no variables
        k_var = res_data[:u′][at](gk_var[1]) # Assume K′ has no attributes? 
        println("($gl_val, $k_var)")
        if haskey(r.k_exprs[at], k_var)
          return r.k_exprs[at][k_var](gl_val, bound_vars)
        else 
          return gl_val
        end
      end
    end
  end)
  gl = decombinatorialize(res_data[:gl], typeof(G), nothing, G_dict)
  gr = decombinatorialize(res_data[:gr], typeof(G), nothing, var_repl)
  u = decombinatorialize(res_data[:u], typeof(G), nothing, nothing)
  w = decombinatorialize(res_data[:w], typeof(G), nothing, var_repl)
  return Dict(:gl=>gl,:gr=>gr, :u=>u,:w=>w)
end 






end # module 
