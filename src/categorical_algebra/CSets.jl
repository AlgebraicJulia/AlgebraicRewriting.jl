module CSets
export extend_morphism, pushout_complement,
       can_pushout_complement, dangling_condition, invert_hom, check_pb,
       gluing_conditions, extend_morphisms, sub_vars,
       Migrate, invert_iso, deattr, var_pullback

using DataStructures: OrderedSet, DefaultDict, IntDisjointSets, find_root!
using StructEquality

using CompTime

using ACSets.DenseACSets: attrtype_type, datatypes, constructor
import ACSets: sparsify
import ACSets: acset_schema

using Catlab
using Catlab.BasicSets

using Catlab.CategoricalAlgebra.Chase: 
  extend_morphism, extend_morphism_constraints

using Catlab.CategoricalAlgebra.Pointwise

import Catlab.CategoricalAlgebra: is_natural, components,
                                  homomorphisms, homomorphism, predicate
using ..Theories 
using ..FinSets: id_condition

# Morphism search 
#################

"""
Given   f: A->C and g: B->C, find all morphisms A->B that make the triangle commute 
```
                ??? 
              A  ⇉  B 
              f ↘ ↙ g
                 C
```
"""
function lift_morphism_constraints(f::ACSetTransformation, g::ACSetTransformation)
  Ob = ob(acset_schema(dom(f)))
  predicates = Dict()
  for o in Ob
    preds = Dict{Int,Set{Int}}()
    for p in parts(dom(f), o)
      pred = Set(preimage(g[o], f[o](p)))
      isempty(pred) && return nothing
      preds[p] = pred
    end
    predicates[o] = preds
  end
  return predicates
end

"""
Invert some (presumed iso) components of an ACSetTransformation (given by s)
"""
function invert_iso(f::ACSetTransformation,
                    s::Union{Nothing,AbstractVector{Symbol}}=nothing)
  S = acset_schema(dom(f))
  s_obs = isnothing(s) ? ob(S) : s
  d = Dict(map(ob(S)) do o 
    o => o ∈ s_obs ? Base.invperm(collect(f[o])) : collect(f[o])
  end)
  return only(homomorphisms(codom(f), dom(f); initial=d))
end

"""
Invert a morphism which may not be monic nor epic. When the morphism is not 
monic, an arbitrary element of the preimage is mapped to. When it is not epic,
a completely arbitrary element is mapped to.
"""
function invert_hom(f::ACSetTransformation; epic::Bool=true,
                    monic::Bool=true, check::Bool=false)
  S = acset_schema(dom(f))
  !check || is_natural(f) || error("inverting unnatural hom")
  if epic && monic return invert_iso(f) end # efficient
  A, B = dom(f), codom(f)
  d = NamedTuple(Dict{Symbol, Vector{Int}}(map(ob(S)) do o 
    o => map(parts(B, o)) do b
      p = preimage(f[o], b)
      if length(p) == 1 return only(p)
      elseif length(p) > 1 return monic ? error("f not monic") : first(p)
      else return epic ? error("f not epic") : 1
      end
    end
  end))

  d2 = NamedTuple(Dict(map(attrtypes(S)) do o 
    o => map(parts(B, o)) do b
      p = preimage(f[o], AttrVar(b))
      if length(p) == 1 return AttrVar(only(p))
      elseif length(p) > 1 return monic ? error("f not monic") : first(p)
      else return epic ? error("f not epic") : AttrVar(1)
      end
    end
  end))
  return ACSetTransformation(B, A; merge(d,d2)...)
end

"""
 Y
  i↘  f_
    X → •
 g_ ↓ ⌟ ↓ f
    • → •   
      g

Check whether (X, f_,g_) is the pullback of (f,g), up to isomorphism (i.e. the 
pullback of f and g produces (Y,π₁,π₂), where Y is isomorphic to X and 
i⋅f_ = π₁ & i⋅g_ = π₂.
"""
function check_pb(f,g,f_,g_; cat)
  @debug "checking pb with f $f\ng $g\nf_ $f_\ng_ $g_"
  codom[cat](f)==codom[cat](g) || error("f,g must be cospan")
  dom[cat](f_)==dom[cat](g_)   || error("f_,g_ must be span")
  codom[cat](f_)==dom[cat](f)  || error("f_,f must compose")
  codom[cat](g_)==dom[cat](g)  || error("g_,g must compose")

  pb_check = limit[cat](Cospan(f, g))
  @debug "apex(pb_check) $(apex(pb_check))"
  isos = isomorphisms(apex(pb_check), dom[cat](f_))
  return any(isos) do i
    all(zip(legs(pb_check), [f_, g_])) do (leg, h)
      force(compose[cat](i, h)) == force(leg)
    end
  end 
end

# Non-monotonicity
##################

"""
Every morphism induces a partition of the parts of the domain. This function 
finds every nontrivial partition (size greater than one element) for the objects
of the schema.
"""
fibers(f::ACSetTransformation) = 
  Dict(o => fibers(f[o]) for o in ob(acset_schema(dom(f))))

function fibers(f::FinFunction)
  dic = DefaultDict{Int,Vector{Int}}(()->Int[])
  for v in dom(f)
    push!(dic[f(v)], v)
  end
  filter(xs->length(xs)>1, collect(values(dic)))
end

unions!(i::IntDisjointSets, xs::Vector{Int}) = if length(xs) > 1 
  [union!(i, x, y) for (x,y) in zip(xs, xs[2:end])]
end

"""Further induced equations between AttrVars, given a specific match morphism"""
function var_eqs(l::ACSetTransformation, m::ACSetTransformation)
  I, L = dom(l), codom(l)
  S = acset_schema(L)
  eq_I = Dict(a => IntDisjointSets(nparts(I, a)) for a in attrtypes(S))
  for (o, xss) in pairs(fibers(m)) # match induces equivalence of ob parts in L
    for xsₗ in xss
      xsᵢ = Vector{Int}(vcat(preimage.(Ref(l[o]), xsₗ)...))
      for (f, _, at) in attrs(S; from=o)
        unions!(eq_I[at], getvalue.(filter(x -> x isa AttrVar, I[xsᵢ, f])))
      end
    end
  end
  return eq_I
end

# Pushout complement
####################

""" Compute pushout complement of attributed C-sets, if possible.

The pushout complement is constructed pointwise from pushout complements of
finite sets. If any of the pointwise identification conditions fail (in FinSet),
this method will raise an error. If the dangling condition fails, the resulting
C-set will be only partially defined. To check all these conditions in advance,
use the function [`can_pushout_complement`](@ref).
"""
@instance ThPushoutComplement{ACSet,ACSetTransformation
                             } [model::ACSetCategory] begin 
  function pushout_complement(pair::ComposablePair) 
    l, m = pair 
    lm = compose[model](l,m)
    I, G = dom(l), codom(m)
    S = acset_schema(I)
    𝒞 = entity_cat(model)
    om(x, o) = ob_map[𝒞](get_ob(model, x, o))

    all(at->nparts(G, at)==0, attrtypes(S)) || error("Cannot rewrite with AttrVars in G")
    # Compute pushout complements pointwise in FinSet.
    comps = NamedTuple(Dict(map(ob(S)) do o 
      𝒟 = entity_attr_cat(model, o)
      component_pair = ComposablePair(l[o], m[o]; cat=𝒟)
      pc = pushout_complement[𝒟](component_pair)
      o => pc
    end))
    k_components = Dict{Symbol,Any}(pairs(map(first, comps)))
    g_components = Dict{Symbol,Any}(pairs(map(last, comps)))
    # # Reassemble components into natural transformations.
    K = constructor(model)
    Ks = Dict(k=>dom[entity_attr_cat(model, k)](v) for (k,v) in g_components)
    mapping = DefaultDict(() -> Dict())
    for k in ob(S)
      for i in ob_map[entity_cat(model)](Ks[k])
        mapping[k][i] = add_part!(K, k)
      end
    end
    mapping_inv = Dict(o=>Dict(v=>k for (k,v) in mapping[o]) for o in keys(mapping))
    g_components2 = Dict(map(collect(g_components)) do (o, comp)
      f = if haskey(mapping_inv, o)
        FinFunction(Dict(k=>comp(v) for (k,v) in mapping_inv[o]), om(K,o), om(G,o))
      else 
        nothing
      end
      o => f
    end)
    g_components2 = Dict(map(collect(g_components)) do (o, comp)
      f = if haskey(mapping_inv, o)
        FinFunction(Dict(k=>comp(v) for (k,v) in mapping_inv[o]), om(K,o), om(G,o))
      else 
        nothing
      end
      o => f
    end)

    for (h,d,c) in arrows(S)
      g_c, g_d = get(g_components2, c, nothing), g_components2[d]
      for p in parts(K, d)
        res = G[g_d(p), h]
        K[p, h] = c ∈ ob(S) ? only(preimage(g_c, res)) : res
      end
    end
    k_components2 = Dict{Symbol,Any}(map(collect(k_components)) do (o, comp)
      f = FinFunction(mapping[o], codom(comp), om(K,o))
      o => postcompose(comp, f)
    end)
    for k in attrtypes(S)
      k_components2[k] = lm[k]
    end

    # need to reindex the components in light of the actual part IDs in K
    g = ACSetTransformation(g_components2, K, G; cat=model)
    k = ACSetTransformation(I, K; cat=model, k_components2...)

    # Optional sanity check
    # kg, lm = force.(compose[model].([k,l], [g, m]))
    # kg == lm || error(
    #   "Square doesn't commute: \n\t$(components(kg)) \n!= \n\t$(components(lm))")

    is_natural(k; cat=model) || error(
      "k unnatural $k $(naturality_failures(k; cat=model))")
    
    is_natural(g; cat=model) || error(
      "g unnatural $(naturality_failures(g; cat=model))")

    return ComposablePair(k, g; cat=model)
  end

  function pushout_complement_violations(pair::ComposablePair)
    viols = []
    for k in keys(components(pair[1]))
      a,b = id_condition(pair[1][k], pair[2][k])
      append!(viols, [("Id: nondeleted ↦ deleted ", k, aa) for aa in a])
      append!(viols,[("Id: nonmonic deleted", k, bb) for bb in b])
    end
    append!(viols, [("Dangling", d...) for d in dangling_condition(pair)])
    return viols
  end
end


"""
Check the dangling condition for a pushout comlement: m doesn't map a deleted
element d to an element m(d) ∈ G if m(d) is connected to something outside the
image of m.

For example, in the C-Set of graphs,

   e1
v1 --> v2

if e1 is not matched but either v1 or v2 are deleted, then e1 is dangling.
"""

dangling_condition(pair::ComposablePair{<:StructACSet{S}}) where S = 
  _dangling_condition(pair, Val{S}, Val{Tuple(ob(S))})

dangling_condition(pair::ComposablePair{<:DynamicACSet}) = let S = acset_schema(first(pair)); 
  runtime(_dangling_condition, pair, S, Tuple(ob(S))) end

@ct_enable function _dangling_condition(pair::ComposablePair{<:ACSet}, @ct(S), @ct(obs))
  l, m = pair
  L, G = codom(l), codom(m)
  del_vector = Set{Int}[]
  @ct_ctrl for o in obs
    image = Set(collect(l[@ct o])) # SMALL
    dels = Set{Int}()
    for pL in parts(L,@ct(o))
      if pL ∉ image push!(dels, m[@ct o](pL)) end 
    end
    push!(del_vector, Set(dels))
  end 
  dels = NamedTuple{obs}(del_vector)
  results = Tuple{Symbol,Int,Int}[]
  @ct_ctrl for (morph, src_obj, tgt_obj) in homs(S)
    for tgt_del in dels[@ct tgt_obj]
      for inc_del in incident(G, tgt_del, @ct(morph))
        if inc_del ∉ dels[@ct src_obj]
          push!(results, (@ct(morph), inc_del, G[inc_del,@ct(morph)]))
        end
      end
    end
  end
  results
end

# Subobjects
############

"""Recursively delete anything, e.g. deleting a vertex deletes its edge"""
function cascade_subobj(X::ACSet, sub)
  sub = Dict([k=>Set(v) for (k,v) in pairs(sub)])
  S = acset_schema(X)
  change = true 
  while change
    change = false 
    for (f,c,d) in homs(S)
      for c_part in sub[c]
        if X[c_part,f] ∉ sub[d]
          change = true 
          delete!(sub[c], c_part)
        end
      end
    end
  end 
  return Dict([k => collect(v) for (k,v) in pairs(sub)])
end

  
  
# Variables
###########

"""
Given a value for each variable, create a morphism X → X′ which applies the 
substitution. We do this via pushout.

  O --> X    where C has AttrVars for `merge` equivalence classes 
  ↓          and O has only AttrVars (sent to concrete values or eq classes 
  C          in the map to C.

`subs` and `merge` are dictionaries keyed by attrtype names

`subs` values are int-keyed dictionaries indicating binding, e.g. 
`; subs = (Weight = Dict(1 => 3.20, 5 => 2.32), ...)`

`merge` values are vectors of vectors indicating equivalence classes, e.g.
`; merge = (Weight = [[2,3], [4,6]], ...)`
"""
function sub_vars(X::ACSet, subs::AbstractDict=Dict(), merge::AbstractDict=Dict(); cat) 
  S = acset_schema(X)
  O, C = [constructor(X)() for _ in 1:2]
  ox_, oc_ = Dict{Symbol, Any}(), Dict{Symbol,Any}()
  for at in attrtypes(S)
    d = get(subs, at, Dict())
    ox_[at] = AttrVar.(filter(p->p ∈ keys(d) && !(d[p] isa AttrVar), parts(X,at)))
    oc_[at] = Any[d[p.val] for p in ox_[at]]
    add_parts!(O, at, length(oc_[at]))

    for eq in get(merge, at, [])
      isempty(eq) && error("Cannot have empty eq class")
      c = AttrVar(add_part!(C, at))
      for var in eq
        add_part!(O, at)
        push!(ox_[at], AttrVar(var))
        push!(oc_[at], c)
      end
    end
  end
  ox = ACSetTransformation(O,X; ox_..., cat)
  oc = ACSetTransformation(O,C; oc_..., cat)
  return first(legs(pushout[cat](ox, oc)))
end 

"""
Take an ACSet pullback combinatorially and freely add variables for all 
attribute subparts.

This relies on implementation details of `abstract`.
"""
function var_pullback(c::Cospan{<:StructACSet{S,Ts}}) where {S,Ts}
  f, g = deattr.(c)
  cat = ACSetCategory(dom(f))
  legs = pullback[cat](f,g)
  new_apex = typeof(dom(first(c)))()
  copy_parts!(new_apex, dom(first(legs))) # has everything except attributes
  for at in attrtypes(S) add_part!(new_apex, at) end 
  for (at,c,_) in attrs(S) 
    new_apex[:,at] = fill(AttrVar(1), nparts(new_apex,c))
  end 
  A = abstract_attributes(new_apex)
  map(zip(legs,c)) do (p,f)
    X = dom(f)
    attr_components = Dict(map(attrtypes(S)) do at
      comp = Union{AttrVar,attrtype_instantiation(S,Ts,at)}[]
      for (f, c, _) in attrs(S; to=at)
        append!(comp, X[f][collect(compose[FinSetC()](A[c],p[c]))])
      end
      return at => comp
    end)
    ACSetTransformation(dom(A),X; components(p)...,attr_components...)
  end
end


function deattr(X::StructACSet{S})::AnonACSet where S
  P = Presentation(FreeSchema)
  add_generators!(P, Ob(FreeSchema, objects(S)...))
  for (h,s,t) in homs(S)
    add_generator!(P, Hom(h, Ob(FreeSchema,s), Ob(FreeSchema,t)))
  end
  aa = AnonACSet(P) # indexing?
  copy_parts!(aa, X)
  return aa
end 

function deattr(f::ACSetTransformation)
  X, Y = deattr.([dom(f),codom(f)])
  S = acset_schema(X)
  return ACSetTransformation(X,Y; Dict(o=>f[o] for o in ob(S))...)
end 

# Simple Δ migrations (or limited case Σ)
#########################################

"""TODO: check if functorial"""
@struct_hash_equal struct Migrate
  cat::ACSetCategory
  obs::Dict{Symbol, Symbol}
  homs::Dict{Symbol, Symbol}
  P1::Presentation
  T1::Type 
  P2::Presentation
  T2::Type 
  delta::Bool 
end 

Migrate(cat::ACSetCategory, s1::Presentation, t1::Type, s2=nothing, t2=nothing; delta=true) = 
Migrate(cat, Dict(x => x for x in Symbol.(generators(s1, :Ob))),
        Dict(x => x for x in Symbol.(generators(s1, :Hom))),
        s1, t1, s2, t2; delta)

Migrate(cat::ACSetCategory, o::Dict, h::Dict, s1::Presentation, t1::Type, s2=nothing, t2=nothing; 
        delta::Bool=true) = Migrate(cat, Dict(collect(pairs(o))),
                                    Dict(collect(pairs(h))), s1, t1, 
                                    isnothing(s2) ? s1 : s2, 
                                    isnothing(t2) ? t1 : t2, 
                                    delta)


sparsify(d::Dict{V,<:ACSet}) where V = Dict([k=>sparsify(v) for (k,v) in collect(d)])
sparsify(d::Dict{<:ACSet,V}) where V = Dict([sparsify(k)=>v for (k,v) in collect(d)])
sparsify(::Nothing) = nothing

(F::Migrate)(d::Dict{V,<:ACSet}) where V = Dict([k=>F(v) for (k,v) in collect(d)])
(F::Migrate)(d::Dict{<:ACSet,V}) where V = Dict([F(k)=>v for (k,v) in collect(d)])
(m::Migrate)(::Nothing) = nothing
(m::Migrate)(s::Union{String,Symbol}) = s
function (m::Migrate)(Y::ACSet; cat=nothing)
  if m.delta
     typeof(Y) <: m.T1 || error("Cannot Δ migrate a $(typeof(Y))")
  end
  S = acset_schema(Y)
  X = m.T2()
  partsX = Dict(c => add_parts!(X, c, nparts(Y, get(m.obs,c,c)))
                for c in ob(S) ∪ attrtypes(S))
  for (f,c,d) in homs(S)
    set_subpart!(X, partsX[c], f, partsX[d][subpart(Y, get(m.homs,f,f))])
  end
  for (f,c,_) in attrs(S)
    set_subpart!(X, partsX[c], f, subpart(Y, get(m.homs,f,f)))
  end
  if !m.delta 
    # undefined attrs (Σ migration) get replaced with free variables
    for (f,c,d) in attrs(acset_schema(X))
      for i in setdiff(parts(X,c), X.subparts[f].m.defined)
        X[i,f] = AttrVar(add_part!(X,d))
      end
    end
  end 
  return X
end 

function (F::Migrate)(f::ACSetTransformation)
  d = Dict(map(collect(pairs(components(f)))) do (k,v)
    fun = v isa CopairedFinDomFunction ? get(v) : v
    get(F.obs,k,k) => map(sort(collect(dom(fun)))) do i 
      e = fun(i)
      if e isa Left
        AttrVar(getvalue(e))
      elseif e isa Right 
        getvalue(e)
      else 
        e 
      end
    end
  end)
  homomorphism(F(dom(f)), F(codom(f)); initial=d, cat=F.cat)
end

(F::Migrate)(s::Multispan) = Multispan(apex(s), F.(collect(s)))
(F::Migrate)(s::Multicospan) = Multicospan(apex(s), F.(collect(s)))
(F::Migrate)(d::AbstractDict) = Dict(get(F.obs,k, k)=>v for (k,v) in collect(d))

end # module
