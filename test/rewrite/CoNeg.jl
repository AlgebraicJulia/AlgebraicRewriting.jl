module TestCoNeg 

using Test
using AlgebraicRewriting, Catlab

# Graphs
########
Grph = ACSetCategory(Graph())

L = Graph(2)
R = ob(terminal[Grph]())
r = Rule{:CoNeg}(create[Grph].([L,R])...)

@withmodel TypedCatWithCoproducts(Grph) (⊕)  begin
  G = path_graph(Graph, 2) ⊕ Graph(1)
  m = ACSetTransformation(L, G; V=[1,3]);
  expected = path_graph(Graph, 2) ⊕ R
  @test is_isomorphic(expected, rewrite_match(r, m; cat=Grph))
end

end # module