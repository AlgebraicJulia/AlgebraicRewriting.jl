module TestAlgorithms 

using Test
using Catlab
using AlgebraicRewriting.Incremental.Algorithms: connected_acset_components 

# test connected_acset_components
#--------------------------------
g1, g2 = path_graph.(Graph, [3, 2]);
ccs, iso = connected_acset_components(g1 ⊕ g2);
@test is_monic(iso) && is_epic(iso)
@test collect(first(ccs.cocone)[:V]) == [1,2,3] 

end 