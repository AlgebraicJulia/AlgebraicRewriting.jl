module CSets
export topo_obs, check_eqs, eval_path, extend_morphism, pushout_complement,
       can_pushout_complement, dangling_condition, invert_hom, check_pb,
       gluing_conditions, extend_morphisms, postcompose_partial, sub_vars,
       combinatorialize

using Catlab, Catlab.Theories, Catlab.Graphs, Catlab.Schemas
using Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.FinSets: IdentityFunction
using Catlab.CategoricalAlgebra.CSets: unpack_diagram, type_components
import ..FinSets: pushout_complement, can_pushout_complement, id_condition
import Catlab.CategoricalAlgebra: is_natural, Slice, SliceHom, components,
                                  LooseACSetTransformation, homomorphisms, homomorphism
import Base: getindex
using DataStructures: OrderedSet
using Catlab.ColumnImplementations: AttrVar


"""
This file contains various extensions / features for C-Sets that are 
particularly helpful for rewriting.
"""

"""Get topological sort of objects of a schema. Fail if cyclic"""
function topo_obs(S::Type)::Vector{Symbol}
  G = Graph(length(ob(S)))
  for (_, s, t) in homs(S)
    add_edge!(G, findfirst(==(s),ob(S)), findfirst(==(t),ob(S)))
  end
  return [ob(S)[i] for i in reverse(topological_sort(G))]
end

"""Confirm a C-Set satisfies its equational axioms"""
function check_eqs(x::StructACSet, pres::Presentation, o::Symbol, i::Int)::Bool
  for (p1,p2) in filter(e->only(e[1].type_args[1].args) == o, pres.equations)
    eval_path(x, p1, i) == eval_path(x,p2, i) || return false
  end
  return true
end

"""
Take a GATExpr (an id morphism, a generator, or a composite) and evaluate,
starting at a particular point.
"""
function eval_path(x::StructACSet, h, i::Int)::Int
  val = i
  for e in h.args
    val = x[val, e]
  end
  return val
end

function extend_morphism_constraints(f::ACSetTransformation,
                                     g::ACSetTransformation
                                     )::Union{Nothing,
                                              Dict{Symbol, Dict{Int,Int}}}
  dom(f) == dom(g) || error("f and g are not a span: $f \n$g")

  init = Dict{Symbol, Dict{Int,Int}}()
  for (ob, mapping) in pairs(components(f))
    init_comp = Pair{Int,Int}[]
    for i in parts(codom(g), ob)
      vs = Set(mapping(preimage(g[ob], i)))
      if length(vs) == 1
        push!(init_comp, i => only(vs))
      elseif length(vs) > 1 # no homomorphism possible
        return nothing
      end
    end
    init[ob] = Dict(init_comp)
  end
  return init
end

"""    extend_morphism(f::ACSetTransformation,g::ACSetTransformation,monic=false)::Union{Nothing, ACSetTransformation}

Given a span of morphisms, we seek to find a morphism B → C that makes a
commuting triangle if possible.

    B
 g ↗ ↘ ?
 A ⟶ C
   f
"""
function extend_morphism(f::ACSetTransformation, g::ACSetTransformation;
                         initial=Dict(), kw...
                         )::Union{Nothing, ACSetTransformation}
  init = extend_morphism_constraints(f,g)
  if isnothing(init) return nothing end
  for (k,vs) in collect(initial)
    for (i, v) in (vs isa AbstractVector ? enumerate : collect)(vs)
      if haskey(init[k], i)
        if init[k][i] != v return nothing end 
      else 
        init[k][i]  = v 
      end
    end
  end
  homomorphism(codom(g), codom(f); initial=NamedTuple(init), kw...)
end

"""Same as `extend_morphism` but returning all such morphisms"""
function extend_morphisms(f::ACSetTransformation, g::ACSetTransformation;
                          initial=Dict(), kw...
                          )::Vector{ACSetTransformation}
  init = extend_morphism_constraints(f,g)
  if isnothing(init) return [] end
  for (k,vs) in collect(initial)
    for (i, v) in (vs isa AbstractVector ? enumerate : collect)(vs)
      if haskey(init[k], i)
        if init[k][i] != v return nothing end 
      else 
        init[k][i]  = v 
      end
    end
  end
  homomorphisms(codom(g), codom(f); initial=NamedTuple(init), kw...)
end

"""
Convert a morphism L->G to a morphism L->H using a partial morphism G->H, 
if possible.

       L ===== L
     m ↓       ↓ m'
       G ↩ K → H

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

""" Compute pushout complement of attributed C-sets, if possible.

The pushout complement is constructed pointwise from pushout complements of
finite sets. If any of the pointwise identification conditions fail (in FinSet),
this method will raise an error. If the dangling condition fails, the resulting
C-set will be only partially defined. To check all these conditions in advance,
use the function [`can_pushout_complement`](@ref).
"""
function pushout_complement(pair::ComposablePair{<:ACSet, <:TightACSetTransformation})
  # Compute pushout complements pointwise in FinSet.
  components = map(pushout_complement, unpack_diagram(pair))
  k_components, g_components = map(first, components), map(last, components)

  # Reassemble components into natural transformations.
  g = hom(Subobject(codom(pair), g_components))
  k = ACSetTransformation(k_components, dom(pair), dom(g))
  return ComposablePair(k, g)
end

"""
If either of the morphisms is Loose, then the composable pair type will just 
be ACSetTransformation (or LooseACSetTransformation if both are Loose)

This is the same code as above but with an extra line to compute the type 
components.
"""
function pushout_complement(pair::ComposablePair{<:ACSet, <:ACSetTransformation})
  S = acset_schema(dom(pair))
  Attr = Tuple(attrtypes(S))

  # Compute pushout complements pointwise in FinSet.
  components = map(pushout_complement, unpack_diagram(pair))
  k_components, g_components = map(first, components), map(last, components)

  # Reassemble components into natural transformations.
  K = dom(hom(Subobject(codom(pair), g_components)))
  tc = Dict(map(Attr) do at 
    at => compose([x[at] for x in type_components.(pair)])
  end)
  for (a, d, _) in attrs(S)
    set_subpart!(K, k_components[d]|>collect, a, dom(pair)[a])
  end
  ps = typeof(dom(pair)).parameters
  icomp = Dict(at=>IdentityFunction(TypeSet(p)) for (at, p) in zip(Attr, ps))
  k = LooseACSetTransformation(k_components, icomp, dom(pair), K)
  g = LooseACSetTransformation(g_components, tc, K, codom(pair))
  return ComposablePair(k, g)
end


function can_pushout_complement(pair::ComposablePair{<:ACSet})
  all(can_pushout_complement, unpack_diagram(pair)) &&
    isempty(dangling_condition(pair))
end

gluing_conditions(pair::ComposablePair{<:Slice}) =
  gluing_conditions(ComposablePair(pair[1].f, pair[2].f))


function gluing_conditions(pair::ComposablePair{<:ACSet})
  viols = []
  for (k,x) in pairs(unpack_diagram(pair))
    a,b = collect.(id_condition(x))
    append!(viols, [("Id: nondeleted ↦ deleted ", k, aa) for aa in a])
    append!(viols,[("Id: nonmonic deleted", k, bb) for bb in b])
  end
  append!(viols, [("Dangling", d...) for d in dangling_condition(pair)])
  return viols
end


"""    pushout_complement(f::SliceHom, g::SliceHom)
Compute a pushout complement in a slice category by using the pushout complement
in the underlying category.

     f
  B <-- A ---⌝
  | ↘ ↙      |
 g|  X       | f′
  ↓ ↗  ↖ cx  |
  D <--- C <--
      g′

"""
function pushout_complement(fg::ComposablePair{Slice})
    f, g = fg
    f′, g′ = pushout_complement(ComposablePair(f.f, g.f))
    D = codom(g)
    C = Slice(compose(g′, D.slice))
    return SliceHom(dom(f), C, f′) => SliceHom(C, D, g′)
end

""" Pushout complement: extend composable pair to a pushout square.

[Pushout complements](https://ncatlab.org/nlab/show/pushout+complement) are the
essential ingredient for double pushout (DPO) rewriting.
"""
pushout_complement(f, g) = pushout_complement(ComposablePair(f, g))

""" Can a pushout complement be constructed for a composable pair?

Even in nice categories, this is not generally possible.
"""
can_pushout_complement(f, g) = can_pushout_complement(ComposablePair(f, g))

"""
Check the dangling condition for a pushout comlement: m doesn't map a deleted
element d to an element m(d) ∈ G if m(d) is connected to something outside the
image of m.

For example, in the C-Set of graphs,

   e1
v1 --> v2

if e1 is not matched but either v1 or v2 are deleted, then e1 is dangling.
"""
function dangling_condition(pair::ComposablePair{<:StructACSet{S}}) where S
  l, m = pair
  orphans = map(components(l), components(m)) do l_comp, m_comp
    image = Set(collect(l_comp))
    Set([ m_comp(x) for x in codom(l_comp) if x ∉ image ])
  end
  # check that for all morphisms in C, we do not map to an orphan
  results = Tuple{Symbol,Int,Int}[]
  for (morph, src_obj, tgt_obj) in homs(S)
    n_src = parts(codom(m), src_obj)
    unmatched_vals = setdiff(n_src, collect(m[src_obj]))
    unmatched_tgt = map(x -> codom(m)[x,morph], collect(unmatched_vals))
    for unmatched_val in setdiff(n_src, collect(m[src_obj]))  # G/m(L) src
      unmatched_tgt = codom(m)[unmatched_val,morph]
      if unmatched_tgt in orphans[tgt_obj]
        push!(results, (morph, unmatched_val, unmatched_tgt))
      end
    end
  end
  results
end

# The following can be deleted when Catlab pull 605 is merged
"""A map f (from A to B) as a map of subobjects of A to subjects of B"""
(f::ACSetTransformation)(X::SubACSet) = begin
  codom(hom(X)) == dom(f) || error("Cannot apply $f to $X")
  Subobject(codom(f); Dict(
    [k=>f.(collect(components(X)[k])) for (k,f) in pairs(components(f))])...)
end


"""
A map f (from A to B) as a map from A to a subobject of B
# i.e. we cast the ACSet A to its top subobject
"""
(f::ACSetTransformation)(X::StructACSet) =
  X == dom(f) ? f(top(X)) : error("Cannot apply $f to $X")


"""
Invert one (presumed iso) component of an ACSetTransformation (given by s)
"""
function invert_hom(f::ACSetTransformation,s::Symbol)::ACSetTransformation
  d = Dict([s=>Base.invperm(collect(f[s]))])
  return ACSetTransformation(codom(f), dom(f); d...)
end
function invert_hom(f::ACSetTransformation{S})::ACSetTransformation where S
  d = Dict(s=>Base.invperm(collect(f[s])) for s in ob(S))
  return ACSetTransformation(codom(f), dom(f); d...)
end



"""
 Y
   ↘  f_
    X → 
 g_ ↓ ⌟ ↓ f
      →   
      g

Check whether (f_,g_) is the pullback of (f,g), up to isomorphism (i.e. the 
pullback produces an object Y which is isomorphic to X, so we need to test, 
for all isos between them, whether i⋅f_ = π₁ && i⋅g_ = π₂).
"""
function check_pb(f,g,f_,g_; verbose=false)
  if verbose println("checking pb with f $f\ng $g\nf_ $f_\ng_ $g_") end
  codom(f)==codom(g) || error("f,g must be cospan")
  dom(f_)==dom(g_) || error("f_,g_ must be span")
  codom(f_)==dom(f) || error("f_,f must compose")
  codom(g_)==dom(g) || error("g_,g must compose")

  pb_check = limit(Cospan(f, g))
  if verbose println("apex(pb_check) $(apex(pb_check))") end
  isos = isomorphisms(apex(pb_check), dom(f_))
  return any(enumerate(isos)) do (n,i)
    if verbose println("n $n") end
    all(zip(force.(legs(pb_check)), [f_, g_])) do (leg, h)
      lft = i ⋅ h
      rght = leg
      lft == rght
    end
  end 
end

# Variables
###########


"""
Given a value for each variable, create a morphism X → X′ which applies the 
substitution.
"""
function sub_vars(X::StructACSet{S}, subs::AbstractDict) where S
  X′ = deepcopy(X)
  comps = Dict(o=>parts(X, o) for o in objects(S))
  for (atr, _, at) in attrs(S)
    for (i, v) in enumerate(X′[atr])
      if v isa AttrVar
        set_subpart!(X′, i, atr, subs[at][i])
      end 
    end
  end 
  for at in attrtypes(S) 
    rem_parts!(X′, at, nparts(X′, at))
  end 
  return TightACSetTransformation(merge(comps, subs), X, X′)
end 


# Combinatorializing ACSets
###########################
"""
StructACSets are converted to AnonACSets which have attributes replaced with 
objects. (DynamicACSets could likewise be converted to other DynamicACSets)

For each attrtype (with `n` AttrVars and `m` distinct concrete values, across all 
attrs which refer to that attrtype) there are n+m parts in pseudoobject. An 
OrderedSet stores, for the m values, what they correspond to. 
"""
function combinatorialize(X::StructACSet{S})::Pair{AnonACSet,Dict} where S
  P = Presentation(FreeSchema)
  add_generators!(P, Ob(FreeSchema, objects(S)..., attrtypes(S)...))
  avals = Dict(k=>OrderedSet() for k in attrtypes(S))
  for (h,s,t) in homs(S)
    add_generator!(P, Hom(h, Ob(FreeSchema,s), Ob(FreeSchema,t)))
  end
  for (h,s,t) in attrs(S)
    add_generator!(P, Hom(h, Ob(FreeSchema,s), Ob(FreeSchema,t)))
    union!(avals[t], filter(x->!(x isa AttrVar), X[h])) 
  end

  aa = AnonACSet(P) # indexing?
  copy_parts!(aa, X)
  for (k,v) in collect(avals) 
    add_parts!(aa, k, length(v))
  end 
  for (h,_,t) in attrs(S)
    aa[h] = [v isa AttrVar ? v.val : findfirst(==(v), avals[t])+nparts(X,t) 
             for v in X[h]]
  end 
  return aa => avals
end 

function combinatorialize(f::ACSetTransformation{S})::Tuple{ACSetTransformation,Dict,Dict} where S
  (cX, dX), (cY, dY) = combinatorialize.([dom(f), codom(f)])

  od = Dict{Symbol, Vector{Int}}([o=>collect(components(f)[o]) for o in objects(S)])
  ad = Dict{Symbol, Vector{Int}}(map(attrtypes(S)) do a 
    a => map(vcat(collect(components(f)[a].fun),collect(dX[a]))) do v 
      if v isa AttrVar 
        return v.val 
      else 
        return findfirst(==(v), dY[a])+nparts(codom(f),a)
      end 
    end 
  end) 
  cs = merge(NamedTuple.([od,ad])...)
  return (TightACSetTransformation(cs, cX, cY), dX, dY)
end 

function decombinatorialize(Xcombo::StructACSet, tX::Type, 
                            vals::Union{Nothing,AbstractDict}=nothing)
  res = tX()
  S = acset_schema(res)
  copy_parts!(res, Xcombo)
  for at in attrtypes(S) rem_parts!(res, at, parts(res, at)) end 
  for (at, c, atype) in attrs(S)
    new_parts = Dict()
    for part in parts(Xcombo, c)
      v = Xcombo[part, at]
      if isnothing(vals)
        if haskey(new_parts, v)
          v_ = new_parts[v]
        else 
          new_parts[v] = v_ = add_part!(res, atype)
        end 
        set_subpart!(res, part, at, AttrVar(v_))
      else 
        set_subpart!(res, part, at, vals[atype][v])
      end
    end
  end
  res
end

function decombinatorialize(f::ACSetTransformation, tX::Type, 
                            domvals=nothing,codomvals=nothing)
  res = tX()
  S = acset_schema(res)
  dcdom = decombinatorialize(dom(f), tX, domvals)
  dccdom = decombinatorialize(codom(f), tX, codomvals)
  comps = NamedTuple(Dict([k=>collect(f[k]) for k in ob(S)]))
  return only(homomorphisms(dcdom,dccdom; initial=comps))
end

# This should be upstreamed as a PR to Catlab
#############################################
is_natural(x::SliceHom) = is_natural(x.f)
components(x::SliceHom) = components(x.f)
Base.getindex(x::SliceHom, c) = x.f[c]

"""
This could be made more efficient as a constraint during homomorphism finding.
"""
function homomorphisms(X::Slice,Y::Slice; kw...)
  map(filter(h->force(X.slice)==force(h⋅Y.slice),
         homomorphisms(dom(X), dom(Y); kw...)) ) do h
    SliceHom(X, Y, h)
  end |> collect
end

function homomorphism(X::Slice,Y::Slice; kw...)
  hs = homomorphisms(X,Y; kw...)
  return isempty(hs) ? nothing : first(hs)
end


# THIS IS PR 710 TO CATLAB
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

(F::DeltaMigration)(s::Multispan) = Multispan(apex(s), F.(collect(s)))
(F::DeltaMigration)(s::Multicospan) = Multicospan(apex(s), F.(collect(s)))

end # module