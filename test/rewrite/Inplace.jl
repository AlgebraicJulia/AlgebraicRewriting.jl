module TestInplace

using Test
using Catlab
using AlgebraicRewriting

@acset_type MADWeightedGraph(SchWeightedGraph, part_type=BitSetParts, index=[:src,:tgt]) <: AbstractGraph
const MADIntGraph = MADWeightedGraph{Int}

L = @acset MADIntGraph begin V=2; E=2; Weight=2; src=1; tgt=2;
                                    weight=AttrVar.(1:2) end
I = MADIntGraph(2)
R = @acset MADIntGraph begin V=2; E=1; Weight=1; src=1; tgt=2;
                                    weight=[AttrVar(1)] end

l = homomorphism(I,L; monic=true)
r = homomorphism(I,R; monic=true)
rule = Rule(l, r; monic=[:E], expr=Dict(:Weight=>[xs->xs[1]+xs[2]]))

G = @acset MADIntGraph begin V=1; E=3; src=1; tgt=1;
                                    weight=[10,20,100] end
# to_graphviz(G; edge_labels=:weight)
m = homomorphism(codom(l), G; monic=[:E])

prog = compile_rewrite(rule)

comps = interp_program!(prog, m.components, G)

dump(G)

f = ACSetTransformation(comps, R, G)

@test f.components[:Weight][1] == 30

end
