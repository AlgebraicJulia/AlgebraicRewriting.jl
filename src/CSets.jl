module CSets
export topo_obs, check_eqs, eval_path, extend_morphism, pushout_complement,
       can_pushout_complement, dangling_condition, is_injective, invert_hom,
       homomorphisms, gluing_conditions

using Catlab, Catlab.Theories, Catlab.Graphs
using Catlab.CategoricalAlgebra: ACSet, StructACSet, ACSetTransformation, ComposablePair, preimage, components, Subobject, parts, SubACSet, SliceHom, force, nparts, legs, apex, pushout, Cospan
using Catlab.CategoricalAlgebra.CSets: unpack_diagram
import ..FinSets: pushout_complement, can_pushout_complement, is_injective, is_surjective, id_condition
import Catlab.CategoricalAlgebra: is_natural, Slice, SliceHom, components
using ..Search
import ..Search: homomorphism, homomorphisms
import Base: getindex


"""Get topological sort of objects of a schema. Fail if cyclic"""
function topo_obs(S::Type)::Vector{Symbol}
  G = Graph(length(ob(S)))
  for (s, t) in zip(S.parameters[5], S.parameters[6])
    add_edge!(G, s, t)
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
  dom(f) == dom(g) || error("f and g are not a span: $jf \n$jg")

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
                         monic=false, iso=false, init_check=true
                         )::Union{Nothing, ACSetTransformation}
  init = extend_morphism_constraints(f,g)
  if isnothing(init) return nothing end
  homomorphism(codom(g), codom(f); initial=NamedTuple(init), monic=monic, iso=iso,
               bindvars=true, init_check=init_check)
end

""" Compute pushout complement of attributed C-sets, if possible.

The pushout complement is constructed pointwise from pushout complements of
finite sets. If any of the pointwise identification conditions fail (in FinSet),
this method will raise an error. If the dangling condition fails, the resulting
C-set will be only partially defined. To check all these conditions in advance,
use the function [`can_pushout_complement`](@ref).
"""
function pushout_complement(pair::ComposablePair{<:ACSet})
  # Compute pushout complements pointwise in FinSet.
  components = map(pushout_complement, unpack_diagram(pair))
  k_components, g_components = map(first, components), map(last, components)

  # Reassemble components into natural transformations.
  g = hom(Subobject(codom(pair), g_components))
  k = ACSetTransformation(k_components, dom(pair), dom(g))
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
  for (morph, src_obj, tgt_obj) in zip(hom(S), dom(S), codom(S))
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

function is_injective(α::ACSetTransformation{S}) where {S}
    for c in components(α)
      if !is_injective(c) return false end
    end
    return true
  end

function is_surjective(α::ACSetTransformation{S}) where {S}
    for c in components(α)
      if !is_surjective(c) return false end
    end
    return true
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

# This should be upstreamed as a PR to Catlab
#############################################
is_natural(x::SliceHom) = is_natural(x.f)
components(x::SliceHom) = components(x.f)
Base.getindex(α::SliceHom, c) = x.f[c]

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

end # module