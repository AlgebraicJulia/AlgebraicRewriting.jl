module TestCoNeg 

using Test
using AlgebraicRewriting, Catlab

# Graphs
########
L = Graph(2)
R = ob(terminal(Graph))
r = Rule{:CoNeg}(create.([L,R])...)

G = path_graph(Graph, 2) ⊕ Graph(1)
m = ACSetTransformation(L, G; V=[1,3]);

expected = path_graph(Graph, 2) ⊕ R
@test is_isomorphic(expected, rewrite_match(r, m))

end # module