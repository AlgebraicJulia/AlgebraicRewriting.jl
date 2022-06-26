module TestVariables
using Revise
using Test
using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra: @acset, @acset_type
using AlgebraicRewriting


@present TheoryLabeledDecGraph(FreeSchema) begin
  (V,E)::Ob
  (src,tgt)::Hom(E,V)
  X::AttrType
  dec::Attr(E,X)
  label::Attr(V,X)
end

@acset_type LabeledDecGraph(TheoryLabeledDecGraph, index=[:src,:tgt])
const LGraph = LabeledDecGraph{Union{Expr, Var, Symbol, String}}

# Rewrite attributes with variable change
#########################################

arrvar = @acset LGraph begin
  V=2;  E=1;  src=1; tgt=2
  dec = [Var(:c)];  label = Var.([:a,:b])
end

avertex= @acset LGraph begin V=1;  label = [Var(:a)] end

revarr = @acset LGraph begin
  V = 2; E = 2; src = [1,2]; tgt = [2,1]
  dec = [Var(:c),:(reverse(c))]; label = [Var(:a),Var(:a)]
end

arrG = @acset LGraph begin
  V=2;  E=1;  src=1; tgt=2
  dec = ["abc"];  label = ["x","y"]
end

expected_res = @acset LGraph begin
  V=2;  E=2;  src=[1,2]; tgt=[2,1]
  dec = ["abc", "cba"];  label = ["x","x"]
end

L = homomorphism(avertex, arrvar);
R = homomorphism(avertex, revarr);
@test is_isomorphic(rewrite(Rule(L,R),arrG), expected_res)

end # module