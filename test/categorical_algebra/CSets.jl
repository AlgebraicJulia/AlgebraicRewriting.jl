module TestCSets
using Test
using Catlab, Catlab.Graphs, Catlab.CategoricalAlgebra
using AlgebraicRewriting


# Pushout complement 
####################

# Simplest non-trivial, non-monic exmaple
@present TheoryFinSet(FreeSchema) begin
  X::Ob
end
@acset_type FinSetType(TheoryFinSet)

I, L, G = [@acset FinSetType begin X=i end for i in [2,1,1]]
l = CSetTransformation(I, L, X=[1,1])
m = CSetTransformation(L, G, X=[1])
@test can_pushout_complement(ComposablePair(l,m))
ik, kg = pushout_complement(ComposablePair(l,m))
# There are 3 functions `ik` that make this a valid P.C.
# codom=1 with [1,1], codom=2 with [1,2] or [2,1]
K = codom(ik)
@test nparts(K, :X) == 1 # algorithm currently picks the first option

# Slices 
########
two = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,1] end

L_ = path_graph(Graph, 2)
L = Slice(ACSetTransformation(L_, two, V=[2,1], E=[2]))

G_ = path_graph(Graph, 3)
G = Slice(ACSetTransformation(G_, two, V=[1,2,1], E=[1,2]))

@test length(homomorphisms(L_, G_)) == 2
@test length(homomorphisms(L, G)) == 1




end # module