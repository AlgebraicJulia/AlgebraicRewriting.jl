module TestCSets
using Test
using Catlab
using Catlab.Graphs
using Catlab.CategoricalAlgebra: @acset, ACSetTransformation, Slice

using AlgebraicRewriting


two = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,1] end

L_ = path_graph(Graph, 2)
L = Slice(ACSetTransformation(L_, two, V=[2,1], E=[2]))

G_ = path_graph(Graph, 3)
G = Slice(ACSetTransformation(G_, two, V=[1,2,1], E=[1,2]))

@test length(homomorphisms(L_, G_)) == 2
@test length(homomorphisms(L, G)) == 1
end # module