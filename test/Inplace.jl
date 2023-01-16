module TestRandom 

using AlgebraicRewriting
using Random: seed! 
seed!(42)


using Test
using Catlab.CategoricalAlgebra, Catlab.Graphs, Catlab.Graphics
const hom = CategoricalAlgebra.homomorphism

# Test inplace deletion
#######################

p3 = path_graph(Graph,4)
p2_p2 = path_graph(Graph, 2) ⊕ path_graph(Graph, 2)
l = hom(p2_p2, p3; monic=true)

G = cycle_graph(Graph, 5);
# to_graphviz(G; node_labels=true)
m = hom(p3, G);

new_l_m = pushout_complement!(l, m )
@test is_natural(new_l_m)
# Fifth edge (5->1) now in position #2 (which was 2->3 but got deleted) 
expected = @acset Graph begin V=5;E=4;src=[1,5,3,4];tgt=[2,1,4,5] end 
@test G == expected
# to_graphviz(G;node_labels=true)

# now we delete the vertices too
l = ACSetTransformation(Graph(2), p3; V=[1,4]);
G = cycle_graph(Graph, 5);
m = hom(p3, G);
new_l_m = pushout_complement!(l, m);
@test is_natural(new_l_m)
# V2, V3 got deleted (now V4↦V3 and V5↦V2)
# new edges are just #4 (4->5, now 3->2) and #5 (5->1, 2->1), shifted to E2,E1. 
expected = @acset Graph begin V=3; E=2; src=[2,3]; tgt=[1,2] end 
@test expected == G
# to_graphviz(G;node_labels=true)

G = Graph(1) ⊕ cycle_graph(Graph, 5);
l = hom(Graph(2), Graph(3); monic=true);
m = ACSetTransformation(Graph(3), G; V=[3,6,1]);
new_l_m = pushout_complement!(l, m )
@test is_natural(new_l_m)
@test collect(components(new_l_m)[:V])==[3,1]
expected = @acset Graph begin V=5;E=5;src=[2,3,4,5,1];tgt=[3,4,5,1,2] end 
@test G == expected 
# to_graphviz(G; node_labels=true)


# Test in place merging 
#######################

# Merging sets w/ id loops
R,I,G = map([4,4,5]) do i 
  @acset Graph begin V=i; E=i; src=1:i; tgt=1:i end
end;
ig = hom(I,G;initial=(V=[2,2,3,4],));
ir = hom(I,R;initial=(V=[1,2,3,3],));
rg = pushout!(ig, ir)
@test is_natural(rg)


# merge because shared preimage of lm 
G,I,R = path_graph(Graph, 3), Graph(2), path_graph(Graph, 2);
lm = hom(I, G; initial=(V=[2,2],));
ir = hom(I,R; monic=true)
rg = pushout!(lm, ir)
expected = @acset Graph begin V=3;E=3;src=[1,2,2];tgt=[2,3,2] end 
@test G == expected
# to_graphviz(G; node_labels=true)


# Applying rules 
################
add_loop = Span(
  id(Graph(1)), 
  hom(Graph(1), apex(terminal(Graph))));
rem_edge = Span(
  hom(Graph(2), path_graph(Graph, 2); monic=true),
  id(Graph(2)))
G = path_graph(Graph, 3);
res = apply_rule!(add_loop, G); 
# to_graphviz(G)

traj = simulate(path_graph(Graph, 3), 
         [add_loop => 1., rem_edge => 1.];
         n=3)

end # module 
