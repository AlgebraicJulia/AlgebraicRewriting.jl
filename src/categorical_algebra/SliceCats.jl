module SliceCats 

using Catlab, GATlab
import Catlab: homomorphism, homomorphisms, acset_schema, is_natural,components
using ..CSets: lift_morphism_constraints
using ..Theories 

# Slices
########


@instance ThPushoutComplement{SliceOb{Ob,Hom}, SliceHom{Ob,Hom}
                             } [model::SliceC{Ob,Hom}] where {Ob,Hom} begin 

  """    pushout_complement(f::SliceHom, g::SliceHom)
  Compute a pushout complement in a slice category by using the pushout complement
  in the underlying category.

         f
    B <------ A 
    | ↘     ↙ |
   g|    X    | f′
    ↓ ↗     ↖ |
    D <------ C
        g′

  """
  function pushout_complement(fg::ComposablePair)
    f, g = fg
    f′, g′ = pushout_complement[model.cat](ComposablePair(f.hom, g.hom))
    A, D = dom[model](f), codom[model](g)
    C = SliceOb(codom(f′), compose[model.cat](g′, D.hom))
    return SliceHom(A,C,f′; cat=model.cat) => SliceHom(C, D, g′; cat=model.cat)
  end

  function pushout_complement_violations(fg::ComposablePair)
    f, g = fg
    pushout_complement_violations[model.cat](ComposablePair(f.hom, g.hom))
  end
end

acset_schema(x::SliceOb) = acset_schema(x.ob)
is_natural(x::SliceHom; cat) = is_natural(x.hom; cat=cat.cat)
components(x::SliceHom) = components(x.hom)
Base.getindex(x::SliceHom, c) = x.hom[c]

"""
This could be made more efficient as a constraint during homomorphism finding.
"""
function homomorphisms(X::SliceOb{Ob,Hom},Y::SliceOb{Ob,Hom}; cat=nothing, kw...) where {Ob,Hom}
  cat = if isnothing(cat) 
    Dispatch(ThCategory, [Ob,Hom])
  elseif cat isa SliceC 
    cat.cat 
  else
    cat
  end
  predicates = lift_morphism_constraints(X.hom, Y.hom)
  isnothing(predicates) && return SliceHom{Ob,Hom}[]
  map(homomorphisms(X.ob, Y.ob; predicates)) do h
    SliceHom(X, Y, h; cat=cat)
  end
end

function homomorphism(X::SliceOb,Y::SliceOb; kw...)
  hs = homomorphisms(X,Y; kw...)
  return isempty(hs) ? nothing : first(hs)
end

end # module