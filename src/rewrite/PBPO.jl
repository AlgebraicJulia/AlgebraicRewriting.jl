module PBPO 
export PBPORule

using Catlab, Catlab.CategoricalAlgebra
import Catlab.CategoricalAlgebra: left, right
using Catlab.CategoricalAlgebra.CSets: backtracking_search, abstract_attributes

using StructEquality
using DataStructures: DefaultDict

using ACSets.DenseACSets: types, attrtype_type
using ..Utils
import ..Utils: 
  rewrite_match_maps, get_matches, get_expr_binding_map, AbsRule, ruletype
using ..Constraints
using ...CategoricalAlgebra
using ...CategoricalAlgebra.CSets: 
  extend_morphism_constraints, var_pullback, remove_freevars, 
  combine_dicts!
  

"""
      l    r 
   L  ⟵ K ⟶ R 
tl ↓     ↓ tk     <== tl, tk must be monic 
   L' ⟵ K'

It is assumed we never want the typing/adherence match to be monic, but we 
can optionally restrict the match L → G to be monic.

We can attach application conditions to both the match morphism as well as the 
adherence morphism. Until morphism search under constraints becomes efficient,
it's sometimes needed to just directly state the adherence morphism as a 
function of the match morphism.
"""
@struct_hash_equal struct PBPORule <: AbsRule
  l::ACSetTransformation
  r::ACSetTransformation
  tl::ACSetTransformation
  tk::ACSetTransformation
  l′::ACSetTransformation
  monic::Union{Bool, Vector{Symbol}}
  acs::Vector{Constraint}
  lcs::Vector{Constraint}
  exprs::Dict 
  k_exprs::Dict
  adherence::Union{Nothing, Function}
  function PBPORule(l,r,tl,tk,l′; monic=true, acs=[], lcs=[], 
                    expr=nothing,k_expr=nothing, adherence=nothing)
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

    return new(l,r,tl,tk,l′, monic, acs, lcs, exprs, k_exprs, adherence)
  end
end

ruletype(::PBPORule) = :PBPO
left(r::PBPORule) = r.l 
right(r::PBPORule) = r.r

(F::Migrate)(r::PBPORule) =
  PBPORule(F(r.l), F(r.r), F(r.tl), F(r.tk), F(r.l′); monic=r.monic,
           acs=F.(r.acs), lcs=F.(r.lcs), expr=F(r.exprs), k_expr=F(r.k_exprs), 
           adherence=r.adherence)


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
PBPO matches consist of *two* morphisms. First, a match m: L → G, and secondly 
a typing G → L′. With attributes, it is not so simple because G has concrete 
values for attributes and L′ may have variables. Therefore, we actually change the 
typing to map out of A, an abstracted version of G (with its attributes replaced 
by variables). So we lift matches L->G to matches L->A, then search α∈Hom(A,L′).

In general, we want α to be uniquely determined by m, so by default `α_unique`  
is set to true.

     m
  L⌟ ⟶ G 
 ||     ↓ α
  L  ⟶ L′
     tl

     m
   L ⟶ G 
tl ↓ ↘a ↑ (abs = partial abstraction. Note `a` is `Labs` in the code.)
   L′⟵ A 
      α

The "strong match" condition we enforce is that: tl⁻¹(α(A)) = a⁻¹(A). This means 
we can deduce precisely what m is by looking at α.

"""
function get_matches(rule::PBPORule, G::ACSet;  initial=nothing, 
                     α_unique=true, random=false, n=-1, kw...)
  S = acset_schema(G)
  res = [] # Quadruples of of (m, Labs, abs, α)
  L = codom(left(rule))

  # Process the initial constraints for match morphism and typing morphism
  if isnothing(initial)
    matchinit, typinit = Dict(), Dict()
  elseif initial isa Union{NamedTuple,AbstractDict}
    matchinit, typinit = Dict(pairs(initial)), Dict()
  elseif length(initial)==2
    matchinit, typinit = [Dict(pairs(x)) for x in initial]
  else 
    error("Unexpected type for `initial` keyword: $initial")
  end 

  # Search for each match morphism
  backtracking_search(L, G; monic=rule.monic, initial=NamedTuple(matchinit),
                      random=random) do m
    m_seen = false # keeps track if α_unique is violated for each new m
    if all(ac->apply_constraint(ac, m), rule.acs)
      @debug "m:  $([k=>collect(v) for (k,v) in pairs(components(m))])"
      
      # Construct partially-abtract version of G. Labs: L->A and abs: A->G 
      Labs, abs = partial_abstract(m)
      A = codom(Labs)
      
      # If we have a built in function to deduce the adherence from the match
      if !isnothing(rule.adherence)
        init = rule.adherence(m)
        # Return nothing if failure
        if !isnothing(init)
          αs = homomorphisms(A, codom(rule.tl); initial=init)
          # Also return nothing if the result is not unique
          if length(αs) ==1 
            push!(res, deepcopy((m, Labs, abs, only(αs))))
          end 
        end
      else 
        # Search for adherence morphisms: A -> L′
        init = extend_morphism_constraints(rule.tl, Labs)
        backtracking_search(A, codom(rule.tl); initial=init, kw...) do α
          @debug "\tα: ", [k=>collect(v) for (k,v) in pairs(components(α))] 

          # Check strong match condition
          strong_match = all(types(S)) do o
            prt = o ∈ ob(S) ? identity : AttrVar
            all(prt.(parts(A,o))) do i 
              p1 = preimage(rule.tl[o],α[o](i))
              p2 = preimage(Labs[o], i)
              p1 == p2
            end
          end
          if strong_match && all(lc -> apply_constraint(lc, α), rule.lcs)
            all(is_natural, [m, Labs, abs, α]) || error("Unnatural match")
            if m_seen  error("Multiple α for a single match $m") end 
            @debug "\tSUCCESS"
            push!(res, deepcopy((m, Labs, abs, α)))
            m_seen |= α_unique
            return length(res) == n
          else
            @debug "\tFAILURE (strong $strong_match)"
            return false
          end
        end
      end
    end
    return length(res) == n
  end 
  return res
end


"""
This construction addresses the following problem: ideally when we 'abstract' 
an ACSet from X to A->X, maps *into* X, say B->X, can be canonically pulled back 
to maps B->A which commute. However, A won't do 
here, because there may not even exist any maps B->A. If B has concrete 
attributes, then those cannot be sent to an AttrVar in A. Furthermore, if B 
has multiple 'references' to an AttrVar (two different edges, each with 
AttrVar(1), sent to two different edges with the same atttribute value in X), 
then there is no longer a *canonical* place to send AttrVar(1) to in A, as there 
is a distinct AttrVar for every single part+attr in X. So we need a construction 
which does two things to A->X, starting with a map B->X. 1.) replaces exactly the 
variables we need with concrete values in order to allow a map B->A, 2.) quotients 
variables in A so that there is exactly one choice for where to send attrvars in 
B such that the triangle commutes.


Starting with a map L -> G (where G has no AttrVars), 
we want the analogous map into a "partially abstracted" version of G that 
has concrete attributes replaced with AttrVars *EXCEPT* for those attributes 
which are mapped to by concrete attributes of L. Likewise, multiple occurences 
of the same variable in L correspond to AttrVars which should be merged in the 
partially-abstracted G.

For example, for a schema with a single Ob and Attr (where all combinatorial 
maps are just {1↦1, 2↦2}):

- L = [AttrVar(1), :foo]
- G = [:bar, :foo, :baz]
- abs(G) = [AttrVar(1), AttrVar(2), AttrVar(3)]
- expected result: [AttrVar(1), :foo, AttrVar(2)]

   L  -> Partial_abs(G)
   ↓          ↑
   G  <-   abs(G)

This function computes the top arrow of this diagram starting with the left 
arrow. The bottom arrow is computed by `abstract_attributes` and the right 
arrow by `sub_vars`. Furthermore, a map from Partial_abs(G) to G is provided.

This is the factorization system arising from a coreflective subcategory.

(see https://ncatlab.org/nlab/show/reflective+factorization+system
 and https://blog.algebraicjulia.org/post/2023/06/varacsets/)

"""
function partial_abstract(lg::ACSetTransformation)
  L, G = dom(lg), codom(lg)
  S = acset_schema(L)
  abs_G = abstract_attributes(G)
  A = dom(abs_G)

  # Construct partially-abstracted G 
  #---------------------------------
  subs = Dict{Symbol,Dict{Int}}()
  merges = Dict{Symbol,Vector{Vector{Int}}}()
  for at in attrtypes(S)
    subdict = Dict{Int, Any}()
    mergelist = DefaultDict{Int,Vector{Int}}(()->Int[])
    for (f, o, _) in attrs(S; to=at)
      for iₒ in parts(L, o)
        var = A[lg[o](iₒ), f].val
        val = L[iₒ, f]
        if val isa AttrVar
          push!(mergelist[val.val], var)
        else
          subdict[var] = val
        end
      end
    end
    subs[at] = subdict
    merges[at] = collect(filter(l->!isempty(l), collect(values(mergelist))))
  end
  pabs_G = sub_vars(dom(abs_G), subs, merges)
  
  # Construct maps 
  #---------------
  prt(o) = o ∈ ob(S) ? identity : AttrVar
  T(o) = o ∈ ob(S) ? Int : Union{AttrVar,attrtype_type(L, o)}

  # The quotienting via `sub_vars` means L->PA determined purely by ob components
  to_pabs_init = Dict{Symbol,Vector{Int}}(map(ob(S)) do o
    o => map(prt(o).(collect(lg[o]))) do i 
      pabs_G[o](only(preimage(abs_G[o], i)))
    end
  end)

  from_pabs_comps = Dict(map(types(S)) do o
    comp = Vector{T(o)}(map(prt(o).(parts(codom(pabs_G), o))) do Pᵢ
      only(unique([abs_G[o](prt(o)(pi)) for pi in preimage(pabs_G[o], Pᵢ)]))
    end)
    o => comp 
  end)

  to_pabs = only(homomorphisms(L, codom(pabs_G); initial=to_pabs_init))
  from_pabs = ACSetTransformation(codom(pabs_G), codom(lg); from_pabs_comps...)
  ComposablePair(to_pabs, from_pabs)
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
  _, _, _, α = mα 
  S = acset_schema(dom(left(rule)))
  gl, u′ = var_pullback(Cospan(α, rule.l′)) # A <-- Gk --> K'
  abs_K = abstract_attributes(dom(left(rule))) # absK -> K 
  u = only(filter(u->force(compose(u,u′))==force(compose(abs_K,rule.tk)), 
                  homomorphisms(dom(abs_K), dom(u′))))
  abs_r = homomorphism(dom(abs_K), codom(right(rule)); 
                       initial=Dict([o=>collect(right(rule)[o]) for o in ob(S)]))
  w, gr = pushout(abs_r, u)

  return Dict(:gl=>gl, :u′=>u′, :u=>u, :gr=>gr, :w=>w)
end


"""
Use exprs and k_exprs to fill in variables introduced by applying the rw rule.
"""
function get_expr_binding_map(rule::PBPORule, mtch, res) 
  # unpack data
  X = codom(res[:w])
  (m, _, ab, _) = mtch

  comps = Dict(map(attrtypes(acset_schema(X))) do at 
    # match morphism data
    bound_vars = Vector{Any}(collect(m[at]))
    # For each variable in the intermediate rewrite state, determine what 
    # it refers to in the original graph and what in K′ it refers to, too.
    G_bound_vars = Vector{Any}(collect(compose(res[:gl][at],ab[at])))
    K_bound_vars = [k isa AttrVar ? k.val : k for k in collect(res[:u′][at])]
    # Functions we associate with K′ variables 
    exprs = haskey(rule.k_exprs,at) ? rule.k_exprs[at] : Dict()
    # Compute a value for each variable in the result
    at => map(parts(X, at)) do x 
      p_r = preimage(res[:w][at], AttrVar(x))
      # If the variable was introduced via R, try to use rule.exprs
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
      # Try to get value via the intermediate graph
      p_k = only(preimage(res[:gr][at], AttrVar(x)))
      ik = K_bound_vars[p_k]
      k_expr = exprs isa AbstractVector ? exprs[ik] : get(exprs, ik, nothing)
      if isnothing(k_expr)
        return G_bound_vars[p_k] # default to corresponding attr in original G
      else 
        return k_expr(G_bound_vars[p_k], bound_vars) # apply custom function
      end
    end
  end)
  return sub_vars(X, comps)
end

end # module 
