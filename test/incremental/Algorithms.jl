module TestAlgorithms 

using Test
using Catlab
using AlgebraicRewriting.Incremental.Algorithms: 
  connected_acset_components, all_subobjects, subobject_cache, 
  to_subobj, deattr, pull_back

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

# Pull_back
#----------
@present SchAttr(FreeSchema) begin 
  X::Ob; D::AttrType; f::Attr(X,D); Y::Ob
end
@acset_type Attr(SchAttr)
D1 = @acset Attr{Symbol} begin X=1; f=[AttrVar(1)]; D=1 end
DXY = @acset Attr{Symbol} begin X=2; f=[:X,:Y] end
DX = @acset Attr{Symbol} begin X=1; f=[:X] end
toX,toY = homomorphisms(D1,DXY)
subX = homomorphism(DX,DXY)
toSubX = homomorphism(D1, DX)

pb = pull_back(subX, toX)
@test dom(pb) == dom(toX)
@test codom(pb) == dom(subX)
@test pb == toSubX
@test isnothing(pull_back(subX, toY))

end # module
