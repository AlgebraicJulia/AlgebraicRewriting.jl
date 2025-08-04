module TestAlgorithms 

using Test
using Catlab
using AlgebraicRewriting.Incremental.Algorithms: 
  connected_acset_components, all_subobjects, subobject_cache, 
  to_subobj, deattr, pull_back

# test connected_acset_components
#--------------------------------
g1_23 = @acset Graph begin V=3; E=1; src=2; tgt=3 end 
ccs, iso = connected_acset_components(g1_23);
@test is_monic(iso) && is_epic(iso)
@test length(legs(ccs)) == 2

# test all_subobjects
#--------------------

@test length(all_subobjects(path_graph(Graph, 2))) == 5

wg = path_graph(WeightedGraph{Symbol}, 3)
wg[:weight] = [:X, AttrVar(add_part!(wg, :Weight))]

so_wg = all_subobjects(wg)
@test all(is_natural,so_wg)
@test length(so_wg) == 13

# Mini benchmark
𝒮 = ACSetCategory(SymmetricGraph())
G = @withmodel TypedCatWithCoproducts(𝒮) (⊕) begin
  SymmetricGraph(3) ⊕ cycle_graph(SymmetricGraph, 3)
end
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
