module PartialMap
export partial_map_classifier_universal_property, partial_map_functor_hom,
      partial_map_classifier_eta
using DataStructures
using Catlab, Catlab.CategoricalAlgebra, Catlab.Schemas
using ..CSets

"""
A functor T, playing the role of Maybe in Set, but generalized to C-Sets.

When called on the terminal object, this produces the subobject classifier:
See Mulry "Partial map classifiers and cartesian closed categories" (1994)

This function specifies what T does on objects. The key properties:
  1. for all X ∈ Ob(C), η(X):X⟶T(X) is monic.
                     m   f                                    ϕ(m,f)
  2. for each span A ↩ X → B, there exists a unique morphism A ⟶ T(B)
     such that (m,f) is the pullback of ϕ(m,f),η(B))

Not only do we add an extra element to each component of the C-Set, but we need
to consider the possibility that a component (with n outgoing morphisms) has any
combination of the targets of those morphisms deleted (like the subobject
classifier, there are different *ways* for something to be deleted).

For example, in Graph, an edge can be deleted that goes between any two vertices
of the graph. We can't map all deleted edges to the same point in T(E) (if we're
going to satisfy that desired property #2), so we need an extra edge in T(E) for
every possibility (from V1 to V2, from V1 to V3, ..., from [Deleted] to V1, ...,
from V2 to [Deleted], ... from [Deleted] to [Deleted]), where [Deleted] is our
name for the extra element added to T(V).

                    [src]     [tgt]
Thus, T(E) ≅ |E| + (|V|+1) × (|V|+1).

In general, T(X) ≅ |X| + ∏ₕ(|T(codom(h))|) for each outgoing morphism h::X⟶Y
- the |X| corresponds to the 'real' elements of X
- the second term corresponds to the possible ways an X can be deleted.
- This recursive formula means we require the schema of the C-set to be acyclic
  otherwise the size is infinite (assumes schema is free).
"""
function partial_map_functor_ob(x::StructCSet{S};
    pres::Union{Nothing, Presentation}=nothing
    )::Pair{StructCSet, Dict{Symbol,Dict{Vector{Int},Int}}} where {S}
  res = deepcopy(x)

  # dict which identifies added elements (of some part o) by the values of its
  # foreign keys
  d = DefaultDict{Symbol,Dict{Vector{Int},Int}}(()->Dict{Vector{Int},Int}())

  hdata = collect(homs(S))
  for o in topo_obs(S)
    homs_cds = [(h,cd) for (h,d,cd) in hdata if d==o] # outgoing morphism data
    if isempty(homs_cds)
      d[o][Int[]] = add_part!(res, o)
    else
      homs, cds = collect.(zip(homs_cds...))
      for c in Iterators.product([1:nparts(res,cd) for cd in cds]...)
        d[o][collect(c)] = v = add_part!(res, o; Dict(zip(homs,c))...)

        # Forbid modifications which violate schema equations
        if !isnothing(pres) && !check_eqs(res, pres, o, v)
          delete!(d[o], collect(c))
          rem_part!(res, o, v)
        end
      end
    end
  end
  return res => d
end

"""
Because the functorial embedding of objects keeps a copy of the original data,
what to do with morphisms is just carry them along. Because our implementation
adds all of the additional stuff afterwards, index-wise, we can use literally
the same data for a morphism lifted from X⟶Y to T(X)⟶T(Y).

However, we still need to map the extra stuff in T(X) to the proper extra stuff
in T(Y).
"""
function partial_map_functor_hom(f::CSetTransformation{S};
    pres::Union{Nothing, Presentation}=nothing)::CSetTransformation where S
  X, Y = dom(f), codom(f)
  (d, _), (cd, cddict) = [partial_map_functor_ob(x; pres=pres) for x in [X,Y]]
  comps, mapping = Dict{Symbol,Vector{Int}}(), Dict()
  hdata = collect(homs(S))

  for (k,v) in pairs(f.components)
    mapping[k] = vcat(collect(v), [nparts(Y, k)+1]) # map extra val to extra
  end

  for o in topo_obs(S)
    comps[o] = map(parts(d, o)) do i
      if i <= nparts(X,o) # use f for elements that are defined
        return f[o](i)
      else  # find which extra elem ∈ T(Y) it maps to (by its outgoing maps)
        outdata = Int[comps[cd][d[i, h]] for (h,c_,cd) in hdata if c_==o]
        return cddict[o][outdata]
      end
    end
  end
  return CSetTransformation(d,cd;comps...)
end

"""
The natural injection from X ⟶ T(X)
When evaluated on the terminal object, this gives the subobject classfier.
"""
function partial_map_classifier_eta(x::StructCSet{S};
    pres::Union{Nothing, Presentation}=nothing)::CSetTransformation where {S}
  codom = partial_map_functor_ob(x; pres=pres)[1]
  d = Dict([k=>collect(v) for (k,v) in pairs(id(x).components)])
  return CSetTransformation(x, codom; d...)
end



"""A partial function is defined by the following span:
                          m   f
                        A ↩ X → B

We compute ϕ(m,f): A ⟶ T(B) such that the following is a pullback square:
     f
  X  ⟶ B
m ↓     ↓ η(B)
  A  ⟶ T(B)
     ϕ

Essentially, ϕ sends elements of A to the 'real' values in T(B) when A is in
the subobject picked out by X. When A is 'deleted', it picks out the right
element of the additional data added by T(B).
"""
function partial_map_classifier_universal_property(
    m::CSetTransformation{S}, f::CSetTransformation{S};
    pres::Union{Nothing, Presentation}=nothing, check=false
    )::CSetTransformation where {S}
  hdata   = collect(homs(S))
  A, B    = codom(m), codom(f)
  ηB      = partial_map_classifier_eta(B;pres=pres)
  Bdict   = partial_map_functor_ob(B; pres=pres)[2]
  TB      = codom(ηB)
  fdata   = DefaultDict{Symbol, Dict{Int,Int}}(()->Dict{Int,Int}())
  res     = Dict{Symbol, Vector{Int}}()
  unknown = Dict{Symbol, Int}()
  is_monic(m) || error("partial map classifier called w/ non monic m $m")
  # Get mapping of the known values
  for (o, fcomp) in pairs(components(f))
    unknown[o] = nparts(TB, o)
    for (aval, fval) in zip(collect(m[o]), collect(fcomp))
      fdata[o][aval] = fval
    end
  end
  # Compute components of phi
  for o in topo_obs(S)
    res[o] = map(parts(A, o)) do i
      if haskey(fdata[o], i)
        return fdata[o][i]
      else # What kind of unknown value is it?
        homdata = [res[cd][A[i, h]] for (h,d,cd) in hdata if d == o]
        return Bdict[o][homdata]
      end
    end
  end
  ϕ = CSetTransformation(A, TB; res...)
  if check
    is_natural(ηB) || error("ηB not natural $ηB")
    is_natural(ϕ) || error("ϕ not natural $ϕ")
    is_isomorphic(apex(pullback(ηB,ϕ)), dom(m)) || error("Pullback incorrect")
  end
  return ϕ
end

end # module
