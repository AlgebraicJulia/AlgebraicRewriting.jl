module Theories

using Catlab
import Catlab.Theories: Ob,Hom,id, create, compose, otimes, ⋅, ⊗, ∇, □, trace, 
                        munit, braid, dom, codom, mmerge
using Catlab.WiringDiagrams.MonoidalDirectedWiringDiagrams: implicit_mmerge


@signature ThTracedMonoidalWithBidiagonals <: ThTracedMonoidalCategory begin
  mmerge(A::Ob)::((A ⊗ A) → A)
  @op (∇) := mmerge
  create(A::Ob)::(munit() → A)
  @op (□) := create
end

@symbolic_model TM{ObExpr,HomExpr} ThTracedMonoidalWithBidiagonals begin
  function otimes(A::Ob, B::Ob) 
    associate_unit(new(A,B), munit)
  end
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  function compose(f::Hom, g::Hom)
    cf = codom(f); dg = dom(g) 
    cf == dg || error("cannot compose \n$cf\nwith \n$dg")
    associate_unit(new(f,g; strict=true), id)
  end
end

mmerge(A::Ports{ThTracedMonoidalWithBidiagonals.Meta.T}, n::Int) = implicit_mmerge(A, n)
trace(X::Ports{ThTracedMonoidalWithBidiagonals.Meta.T}, A::Ports{ThTracedMonoidalWithBidiagonals.Meta.T},
  B::Ports{ThTracedMonoidalWithBidiagonals.Meta.T}, f::WiringDiagram{ThTracedMonoidalWithBidiagonals.Meta.T}) = trace(X, f)

end # module 
