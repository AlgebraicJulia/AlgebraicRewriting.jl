module Constraints

using ...Rewrite: Constraint, Rule

using Catlab

using ...CategoricalAlgebra.CSets: extend_morphism
using ...Rewrite: AppCond
import Catlab: codom

using StructEquality

# Application conditions
#-----------------------
"""
An application condition (w/r/t a pattern, L) is given by a morphism out of L.
This can be given two semantics, based on the existence of a particular 
morphism making a triangle commute. We can furthermore impose monic 
constraints on that derived morphism.
"""
abstract type AC end

"""
Coerce a general `Constraint` into a simple application condition, if possible. 
This works if the `Constraint` was created by `AppCond`.
"""
function AC(c::Constraint, dpo=[])
  m = c.g[1,:elabel]
  monic = c.d.expr.monic
  AppCond(m; monic) == c && return PAC(m, monic)
  AppCond(m, false; monic) == c && return NAC(m, monic, dpo)
  return nothing
end

codom(ac::AC) = codom(ac.m)

"""
A negative application condition L -> N means a match L -> X is invalid if 
there exists a commuting triangle.  

We cache the subobjects of ~N (our best approximation to the things that are in
N but not in L), as this can be taken advantage of in detecting new matches
when we delete something.

dpo argument allows us to pass in a morphism I->L so that we can compute the 
staticly known overlaps beforehand, rather than at runtime. These are partial 
overlaps between N and L, which enumerate the possible ways a part of N can be 
sent to something that is deleted (part of L/I).
"""
@struct_hash_equal struct NAC <: AC 
  m::ACSetTransformation
  monic::Vector{Symbol}
  m_complement::ACSetTransformation
  subobj::Vector{ACSetTransformation}
  overlaps::Dict{ACSetTransformation, Vector{Span}}
  function NAC(m, monic, dpos)
    m_comp = hom(~Subobject(m))
    subobjs = hom.(last(subobject_graph(dom(m_comp))))
    subobjs_L = hom.(last(subobject_graph(dom(m))))
    Ob = ob(acset_schema(dom(m)))
    part_N = partition_image(m)
    overlaps = Dict(map(dpos) do dpo
      part_L = partition_image(dpo)
      spans = Set{Span}()
      for subobj in subobjs_L
        all(o->isempty(collect(subobj[o]) ∩ part_L[o][2]), Ob) && continue
        for h in homomorphisms(dom(subobj), codom(m);)
          if !all(o -> isempty(collect(h[o]) ∩ part_N[o][2]), Ob)
            spn = Span(subobj, h)
            spn ∈ spans && error("We shouldn't have duplicates")
            push!(spans, spn)
          end
        end
      end
      dpo => collect(spans)
    end)
    new(m, monic, m_comp, subobjs, overlaps)
  end
end

"""Get the pairs for each component of the image and its component"""
partition_image(f::ACSetTransformation) = Dict(map(ob(acset_schema(dom(f)))) do o
  del,nondel = Set(parts(codom(f), o)), Set{Int}()
  for p in parts(dom(f), o) 
    push!(nondel, f[o](p))
    delete!(del, f[o](p))
  end
  o => (nondel, del)
end)

Base.haskey(n::NAC, k) = haskey(n.overlaps, k)

Base.getindex(n::NAC, k) = n.overlaps[k]

NAC(n::NAC) = n

NAC(m::ACSetTransformation, b::Bool=false, dpo=[]) = 
  NAC(m, b ? ob(acset_schema(dom(m))) : [], dpo)

"""
A negative application condition L -> N means a match L -> X is invalid if 
there does not exist a commuting triangle.  
"""
@struct_hash_equal struct PAC <: AC
  m::ACSetTransformation
  monic::Union{Bool, Vector{Symbol}}
end

PAC(p::PAC) = p

PAC(m::ACSetTransformation, b::Bool=false) = 
  PAC(m, b ? ob(acset_schema(dom(m))) : [])



"""
We may not be merely interested maintaining a set of matches 
Hom(L,X), but instead we care only about the monic morphisms, or morphisms that 
satisfy some positive/negative application conditions (PAC/NAC). In particular, 
NAC poses a new challenge: deletion can introduce new matches. There are various
ways of dealing with this, one of which would require predeclaring `deletion` 
morphisms `L ↢ I`. However, that approach would only work for DPO. So a less 
efficient approach that uses only the data of X ↢ X′ and I→N is to search for 
all morphisms that send *some* part of N to a deleted part of X and all of L to
the nondeleted part of X (this will find all of the new morphisms, only the 
new morphisms, but will possibly contain duplicates).

TODO add `dangling` field
"""
@struct_hash_equal struct IncConstraints 
  monic::Vector{Symbol}
  pac::Vector{PAC}
  nac::Vector{NAC}
end

Base.isempty(c::IncConstraints) = all(isempty, [c.monic,c.pac,c.nac])

"""
Check whether a putative hom meets the constraints. Kwargs control which checks 
are run. Often these homs are generated via hom search using the monic 
constraint, so the monic constraint is usually not checked.
"""
function can_match(constr::IncConstraints, m::ACSetTransformation; 
                    monic::Bool=false, pac=true, nac=true)::Bool

  !monic || all(o -> is_monic(m[o]), constr.monic) || return false

  if pac 
    for ac in constr.pac
      isnothing(extend_morphism(m, ac.m;  monic=ac.monic)) && return false
    end
  end
  
  if nac 
    for ac in constr.nac
      isnothing(extend_morphism(m, ac.m;  monic=ac.monic)) || return false
    end
  end
  
  return true
end

"""
Check if a rule imposes the same constraints as captured by an IncConstraint

TODO handle dangling condition specially (add it as a field to IncConstraints) 
"""
function compat_constraints(constr::IncConstraints, r::Rule{T}) where T
  # (T == DPO && constr.dangling == left(r)) || return false
  cm, rm = Set.([constr.monic, r.monic])
  cm == rm || return "Monic mismatch: $cm != $rm"
  for c in AC.(r.conditions)
    if c isa PAC 
      any(pac -> pac.m == c.m && pac.monic == c.monic, constr.pac
        ) || return "PAC mismatch"
    elseif c isa NAC 
      any(nac -> nac.m == c.m && nac.monic == c.monic, constr.nac
      ) || return "PAC mismatch"
    else 
      return "Rule contains non-AC constraint"
    end
  end 
  return nothing
end

end # module