module TestSPO

using Test, Catlab, AlgebraicRewriting

Grph = ACSetCategory(Graph())
# Removing edges 
#---------------
p2, g2 = path_graph(Graph, 2), Graph(2)
f = homomorphism(g2, p2; initial=(V=1:2,))
r = Rule{:SPO}(f, id[Grph](g2))
r2 = Rule{:SPO}(create[Grph](Graph(1)), id[Grph](Graph()))
@test rewrite(r, p2) == Graph(2)
m = get_match(r2, p2; cat=Grph)
@test rewrite_match(r2, m; cat=Grph) == Graph(1)



# Removing vertices and edges
#----------------------------

A = path_graph(Graph, 3);
K = path_graph(Graph, 2);
B = path_graph(Graph, 2);
add_edge!(B, 2, 2);
C = path_graph(Graph, 4);
add_edge!(C, 1, 3);
ka = path_graph(Graph, 2);
ka, kb = [ACSetTransformation(K, x, V=[1,2], E=[1]) for x in [A,B]];
ac = ACSetTransformation(A, C, V=[1,2,3], E=[1,2]);

"""
Delete the third vertex of • → • → • → • and add a loop to the second vertex.
                             ↘---↗
"""
spr = rewrite_match(Rule{:SPO}(ka,kb), ac; cat=Grph)
@test is_isomorphic(spr, @acset Graph begin V=3; E=2; src=[1,2]; tgt=2 end)



# Semisimplicial sets
#####################
@present ThSemisimplicialSet(FreeSchema) begin
  (V,E,T) :: Ob
  (d1,d2,d3)::Hom(T,E)
  (src,tgt) :: Hom(E,V)
  compose(d1, src) == compose(d2, src)
  compose(d1, tgt) == compose(d3, tgt)
  compose(d2, tgt) == compose(d3, src)
end
@acset_type SSet(ThSemisimplicialSet)
𝒞 = ACSetCategory(SSet())

quadrangle = @acset SSet begin
  T=2; E=5; V=4
  d1=[1,1]
  d2=[2,3]
  d3=[4,5]
  src=[1,1,1,2,3]
  tgt=[4,2,3,4,4]
end

L = quadrangle  # We defined quadrilateral above.
I = @acset SSet begin
  E=4; V=4
  src=[1,1,2,3]
  tgt=[2,3,4,4]
end
R = @acset SSet begin
  T=2; E=5; V=4
  d1=[2,3]
  d2=[1,5]
  d3=[5,4]
  src=[1,1,2,3,2]
  tgt=[2,3,4,4,3]
end
edge = @acset SSet begin E=1; V=2; src=[1]; tgt=[2] end

Tri = @acset SSet begin
  T=1; E=3; V=3;
  d1=[1]; d2=[2]; d3=[3];
  src=[1,1,2]; tgt=[3,2,3]
end


r = Rule{:SPO}(homomorphisms(edge, Tri)[2], id[𝒞](edge); cat=𝒞)
r_dpo = Rule(r.L, r.R)

m = homomorphism(Tri, quadrangle; initial=(V=[1,2,4],))

# This does not make sense for DPO
@test !can_pushout_complement[𝒞](ComposablePair(r.L, m))
@test_throws ErrorException rewrite_match_maps(r_dpo, m; cat=𝒞, check=true)
@test is_isomorphic(rewrite_match(r, m; cat=𝒞),
                    @acset SSet begin E=2; V=3; src=1; tgt=[2,3] end)

# Attributed rewrite
#-------------------
WG = WeightedGraph{Int}
𝒞WG = ACSetCategory(VarACSetCat(WG()))
r = Rule{:SPO}(create[𝒞WG](WG(1)), id[𝒞WG](WG()); cat=𝒞WG)
G = @acset WG begin V=4; E=3; Weight=2; src=[1,2,3]; tgt=[2,3,4]; weight=[3,4,5] end
@test only(rewrite(r,G; initial=(V=[2],), cat=𝒞WG)[:weight]) == 5
@test only(rewrite(r,G; initial=(V=[3],), cat=𝒞WG)[:weight]) == 3

end # module 
