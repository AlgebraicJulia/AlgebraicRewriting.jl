module CSets
export topo_obs, check_eqs, eval_path, extend_morphism, pushout_complement,
       can_pushout_complement, dangling_condition, invert_hom, check_pb,
       gluing_conditions, extend_morphisms, postcompose_partial, sub_vars,
       Migrate, invert_iso, deattr, var_pullback, remove_freevars

using Catlab, Catlab.Theories, Catlab.Graphs, Catlab.Schemas
using Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.FinSets: IdentityFunction
using Catlab.CategoricalAlgebra.CSets: unpack_diagram, type_components
import ..FinSets: pushout_complement, can_pushout_complement, id_condition
import Catlab.ACSetInterface: acset_schema
import Catlab.CategoricalAlgebra: is_natural, Slice, SliceHom, components,
                                  LooseACSetTransformation, homomorphisms, 
                                  homomorphism
using Catlab.DenseACSets: attrtype_type

import Base: getindex
using DataStructures: OrderedSet
using StructEquality


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

"""
Given a span of morphisms, we seek to find all morphisms B → C that make a
commuting triangle.

    B
 g ↗ ↘ ?
 A ⟶ C
   f
"""
function extend_morphism_constraints(f::ACSetTransformation{S},
                                     g::ACSetTransformation{S}
                                     ) where S
  dom(f) == dom(g) || error("f and g are not a span: $f \n$g")

  init = Dict() # {Symbol, Dict{Int,Int}}
  for (ob, mapping) in pairs(components(f))
    init_comp = [] # Pair{Int,Int}
    is_var = ob ∈ attrtypes(S)
    for i in parts(codom(g), ob)
      p = preimage(g[ob], is_var ? AttrVar(i) : i )
      vs = Set(mapping(is_var ? AttrVar.(p) : p))
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
function postcompose_partial(kgh::Span, m::ACSetTransformation{S,Ts}; 
                             check::Bool=false) where {S,Ts}
  kg, kh = kgh
  L = dom(m)
  if codom(m) != codom(kg) 
    show(stdout,"text/plain",codom(m))
    show(stdout,"text/plain",codom(kg))
    error("inconsistent match + partial map ")
  end
  H = codom(kh)
  all(o->is_monic(kg[o]),ob(S)) || error("postcompose partial left leg must be monic $(collect.(collect(pairs(components(kg)))))")
  is_natural(kg) || error("unnatural kg")
  is_natural(kh) || error("unnatural kh")
  is_natural(m) || error("unnatural m")
  fake_res = m ⋅ invert_hom(kg; monic=true, epic=false) ⋅ kh 
  res_comps = Dict{Symbol,Any}(o=>collect(fake_res[o]) for o in ob(S))
  for at in attrtypes(S)
    mapping = Union{attrtype_type(apex(kgh), at),AttrVar}[
      AttrVar(0) for _ in parts(L, at)]
    for (f, c, _) in attrs(S; to=at)
      for (i,fi) in enumerate(L[f])
        if fi isa AttrVar 
          mapping[fi.val] = H[fake_res[c](i), f]
        end
      end
    end
    all(!=(AttrVar(0)), mapping) || error("unbound var in L! mapping $mapping")
    res_comps[at] = mapping 
  end 
  res = ACSetTransformation(L,H; res_comps...)
  !check || is_natural(res) || error("unnatural composed")
  return res
 end

""" Compute pushout complement of attributed C-sets, if possible.

The pushout complement is constructed pointwise from pushout complements of
finite sets. If any of the pointwise identification conditions fail (in FinSet),
this method will raise an error. If the dangling condition fails, the resulting
C-set will be only partially defined. To check all these conditions in advance,
use the function [`can_pushout_complement`](@ref).
"""
function pushout_complement(pair::ComposablePair{<:ACSet, <:TightACSetTransformation{S}}) where S
  p1,p2 = pair 
  I = dom(p1)
  # Compute pushout complements pointwise in FinSet.
  components = NamedTuple(Dict([o=>pushout_complement(ComposablePair(p1[o],p2[o])) for o in types(S)]))
  k_components, g_components = map(first, components), map(last, components)

  # Reassemble components into natural transformations.
  g = hom(Subobject(codom(pair), NamedTuple(Dict(o=>g_components[o] for o in ob(S)))))
  K = dom(g)
  # k_c = Dict([[o=>k_components[o] for o in ob(S)]...,
  #             [at=>k_components[at] for at in attrtypes(S)]...])
  kinit = Dict(o=>collect(k_components[o]) for o in ob(S))
  k = only(homomorphisms(I, K; initial=kinit))

  # Fix variable attributes
  for (at, d, cd) in attrs(S)
    for ivar in AttrVar.(parts(I, cd))
      for dᵢ in incident(I, ivar, at)
        set_subpart!(K, k[d](dᵢ), at, k[cd](ivar))
      end
    end
  end 
  # compose(k,g) == compose(p1,p2) || error("Square doesn't commute")
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
  orphans = Dict(map(ob(S)) do o
    l_comp,m_comp = l[o], m[o]
    image = Set(collect(l_comp))
    o=>Set([ m_comp(x) for x in codom(l_comp) if x ∉ image ])
  end)
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
function (f::ACSetTransformation{S})(X::SubACSet)  where S
  codom(hom(X)) == dom(f) || error("Cannot apply $f to $X")
  comps = Dict(map(ob(S)) do k
    k=>(f[k]).(collect(components(X)[k]))
  end)
  
  Subobject(codom(f); comps...)
end


"""
A map f (from A to B) as a map from A to a subobject of B
# i.e. we cast the ACSet A to its top subobject
"""
(f::ACSetTransformation)(X::StructACSet) =
  X == dom(f) ? f(top(X)) : error("Cannot apply $f to $X")


"""
Some (presumed iso) components of an ACSetTransformation (given by s)
"""
function invert_iso(f::ACSetTransformation{S},
                    s::Union{Nothing,AbstractVector{Symbol}}=nothing) where S
  s_obs = isnothing(s) ? ob(S) : s
  d = Dict(map(ob(S)) do o 
    o => o ∈ s_obs ? Base.invperm(collect(f[o])) : collect(f[o])
  end)
  return ACSetTransformation(codom(f), dom(f); d...)
end

"""
Invert a morphism which may not be monic nor epic. When the morphism is not 
monic, an arbitrary element of the preimage is mapped to. When it is not epic,
an arbitrary element of the domain is mapped to.
"""
function invert_hom(f::ACSetTransformation{S}; 
                    epic::Bool=true,monic::Bool=true, check::Bool=false) where S
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
        set_subpart!(X′, i, atr, subs[at][v.val])
      end 
    end
  end 
  for at in attrtypes(S) 
    rem_parts!(X′, at, parts(X′, at))
  end 
  return TightACSetTransformation(merge(comps, subs), X, X′)
end 

"""
For any ACSet, X, a canonical map A→X where A has distinct variables for all
subparts.
"""
function abstract(X::StructACSet{S,Ts}; check::Bool=false) where {S,Ts} 
  A = deepcopy(X); 
  comps = Dict{Any,Any}(map(attrtypes(S)) do at
    rem_parts!(A, at, parts(A,at))
    comp = Union{AttrVar,attrtype_instantiation(S,Ts,at)}[]
    for (f, d, _) in attrs(S; to=at)
      append!(comp, A[f])
      A[f] = AttrVar.(add_parts!(A, at, nparts(A,d)))
    end 
    at => comp
  end)
  for o in ob(S) comps[o]=parts(X,o) end
  res = ACSetTransformation(A,X; comps...)
  !check || is_natural(res) || error("bad abstract $comps")
  return res
end 


"""
Take an ACSet pullback combinatorially and freely add variables for all 
attribute subparts.

TODO do var_limit, more generally

This relies on implementation details of `abstract`.
"""
function var_pullback(c::Cospan{<:StructACSet{S,Ts}}) where {S,Ts}
  f, g = deattr.(c)
  legs = pullback(f,g)
  new_apex = typeof(dom(first(c)))()
  copy_parts!(new_apex, dom(first(legs))) # has everything except attributes
  for at in attrtypes(S) add_part!(new_apex, at) end 
  for (at,c,_) in attrs(S) 
    new_apex[:,at] = fill(AttrVar(1), nparts(new_apex,c))
  end 
  A = abstract(new_apex)
  map(zip(legs,c)) do (p,f)
    X = dom(f)
    attr_components = Dict(map(attrtypes(S)) do at
      comp = Union{AttrVar,attrtype_instantiation(S,Ts,at)}[]
      for (f, c, _) in attrs(S; to=at)
        append!(comp, X[f][collect(A[c]⋅p[c])])
      end
      return at => comp
    end)
    ACSetTransformation(dom(A),X; components(p)...,attr_components...)
  end
end


"""
We may replace some ...
"""
function remove_freevars(X::StructACSet{S}) where S 
  X = deepcopy(X)
  d = Dict(map(attrtypes(S)) do at
    vs = Set{Int}()
    for f in attrs(S; to=at, just_names=true)
      for v in filter(x->x isa AttrVar, X[f])
        push!(vs, v.val)
      end
    end
    # Get new variable IDs 
    svs = sort(collect(vs))
    vdict = Dict(v=>k for (k,v) in enumerate(svs))
    n_v = length(vdict)
    rem_parts!(X,at, parts(X,at)[n_v+1:end])
    for f in attrs(S; to=at, just_names=true)
      for (v,fv) in filter(v_->v_[2] isa AttrVar,collect(enumerate(X[f])))
        X[v,f] = AttrVar(vdict[fv.val])
      end
    end
    return at => svs
  end)
  return X => d
end 

function remove_freevars(f::ACSetTransformation{S}; check::Bool=false) where S 
  !check || is_natural(f) || error("unnatural freevars input")
  X, d = remove_freevars(dom(f))
  comps = Dict{Symbol,Any}(o=>collect(f[o]) for o in ob(S))
  for at in attrtypes(S)
    comps[at] = collect(f[at])[d[at]]
  end 
  res = ACSetTransformation(X, codom(f); comps...)
  !check || is_natural(res) || error("unnatural freevars output")
  return res 
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

function deattr(f::ACSetTransformation{S}) where S
  X, Y = deattr.([dom(f),codom(f)])
  return ACSetTransformation(X,Y; Dict(o=>f[o] for o in ob(S))...)
end 

# This should be upstreamed as a PR to Catlab
#############################################
acset_schema(x::Slice) = acset_schema(dom(x))
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

"""To do: check if functorial"""
@struct_hash_equal struct Migrate
  obs::Dict{Symbol, Symbol}
  homs::Dict{Symbol, Symbol}
  T1::Type 
  T2::Type 
  Migrate(o,h,t1,t2=nothing) = new(
    Dict(collect(pairs(o))),Dict(collect(pairs(h))),t1,isnothing(t2) ? t1 : t2)
end 
function (m::Migrate)(Y::ACSet)
  typeof(Y) <: m.T1 || error("Cannot migrate a $x")
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
  return X
end 

function (F::Migrate)(f::TightACSetTransformation{S}) where {S} 
  d = Dict(map(collect(pairs(components(f)))) do (k,v)
    get(F.obs,k,k) => v
  end)
  TightACSetTransformation(NamedTuple(d), F(dom(f)), F(codom(f)))
end

(F::Migrate)(s::Multispan) = Multispan(apex(s), F.(collect(s)))
(F::Migrate)(s::Multicospan) = Multicospan(apex(s), F.(collect(s)))
(F::Migrate)(d::AbstractDict) = Dict(get(F.obs,k, k)=>v for (k,v) in collect(d))

end # module