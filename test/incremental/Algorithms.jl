module TestAlgorithms 

using Test
using Catlab
using AlgebraicRewriting.Incremental.Algorithms: 
  connected_acset_components, all_subobjects, subobject_cache, 
  to_subobj, deattr, all_epis

# Test all_epis 
#--------------
@present SchF(FreeSchema) begin (A,B)::Ob; f::Hom(A,B)end
@acset_type Fun(SchF)

X = @acset Fun begin A=3; B=3; f=[1,1,2] end
r = all_epis(X)

grph(x::ACSet) = to_graphviz(x; node_labels=true)
grph(x::ACSetTransformation) = to_graphviz(x; node_labels=true)
cmp(x...) = force(compose(x...))
G = Graph(3)
r = all_epis(G); 

length(r)
length(unique(force.(r)))
unique(force.(r))
codom.(unique(force.(r)))

par = @acset Graph begin V=2; E=2; src=1; tgt=2 end
@time r = all_epis(par ⊕ par); 

#println(length(e))


@test length(all_epis(path_graph(Graph, 2))) == 2
@test length(all_epis(path_graph(Graph, 3))) == 6

# test connected_acset_components
#--------------------------------
g1, g2 = path_graph.(Graph, [3, 2]);
ccs, iso = connected_acset_components(g1 ⊕ g2);
@test is_monic(iso) && is_epic(iso)
@test collect(first(ccs.cocone)[:V]) == [1,2,3] 

# test all_subobjects
#--------------------

@test length(all_subobjects(g2)) == 5

wg = path_graph(WeightedGraph{Symbol}, 3)
wg[:weight] = [:X, AttrVar(add_part!(wg, :Weight))]

so_wg = all_subobjects(wg)
@test all(is_natural,so_wg)
@test length(so_wg) == 13

@test length(all_subobjects(g2)) == 5

# Mini benchmark
G = SymmetricGraph(3) ⊕ cycle_graph(SymmetricGraph, 3)
@time x1 = all_subobjects(G);
@time x2 = subobject_graph(G)[2]; # should be much longer than all_subobjects
@test length(x1) == length(x2) # yet give same result


# Deattr
#--------
@test deattr(SchWeightedGraph) == SchGraph


end # module
