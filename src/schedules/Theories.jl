module Theories

using Catlab, Catlab.Theories, Catlab.WiringDiagrams
import Catlab.Theories: Ob,Hom,id, create, compose, otimes, ⋅, ⊗, ∇,□, trace, munit, braid, dom, codom, mmerge
using Catlab.WiringDiagrams.MonoidalDirectedWiringDiagrams: implicit_mmerge


@signature ThTracedMonoidalWithBidiagonals{Ob,Hom} <: ThTracedMonoidalCategory{Ob,Hom} begin
  mmerge(A::Ob)::((A ⊗ A) → A)
  @op (∇) := mmerge
  create(A::Ob)::(munit() → A)
  @op (□) := create
end

@syntax TM{ObExpr,HomExpr} ThTracedMonoidalWithBidiagonals begin
  otimes(A::Ob, B::Ob) = associate_unit(new(A,B), mzero)
  otimes(f::Hom, g::Hom) = associate(new(f,g))
  function compose(f, g)
    cf = codom(f); dg = dom(g) 
    if cf != dg println("$cf\n$dg") end 
    associate_unit(new(f,g; strict=true), id)
  end
end
# compose(f::TM.Hom{S}, g::TM.Hom{T}) where {S,T} = compose(TM.Hom(f),TM.Hom(g))

mmerge(A::Ports{ThTracedMonoidalWithBidiagonals}, n::Int) = implicit_mmerge(A, n)
trace(X::Ports{ThTracedMonoidalWithBidiagonals}, A::Ports{ThTracedMonoidalWithBidiagonals},
  B::Ports{ThTracedMonoidalWithBidiagonals}, f::WiringDiagram{ThTracedMonoidalWithBidiagonals}) = trace(X, f)

end # module 
