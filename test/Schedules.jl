module TestSchedules

using Test
using Revise
using Catlab, Catlab.Graphs, Catlab.CategoricalAlgebra
using AlgebraicRewriting
using AlgebraicRewriting.Schedules: RWStep

const hom = Catlab.CategoricalAlgebra.homomorphism

G0,G1,G2,G3 = Graph.([0,1,2,3])
# Delete a node
R1 = Span(create(G1), id(G0));
# Merge two nodes
R2 = Span(id(G2), hom(G2, G1));
# Add a node
R3 = Span(id(G0), create(G1))

### Trajectory
G13 = ACSetTransformation(G1,G3;V=[3])
S1 = Span(id(G2), hom(G2,G3;monic=true))
TS1 = RWStep(R3, S1, create(G2), G13); # add #3
S2 = Span(hom(G2,G3;monic=true), id(G2))
TS2 = RWStep(R1, S1, G13, id(G2)); # remove #3


end # module