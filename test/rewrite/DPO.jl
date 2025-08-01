module TestDPO 

using Test, Catlab, AlgebraicRewriting

# Graphs
########
Grph = ACSetCategory(Graph())

# Example graphs
I2 = Graph(2)
I3 = Graph(3)
#   e1   e2
# 1 <- 2 -> 3
span = @acset Graph begin V=3;E=2;src=[2,2];tgt=[1,3] end
# 1 -> 2
arr = path_graph(Graph, 2)
# 1 <-> 2
biarr = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,1] end
# 1 -> 2 -> 3 -> 1
tri = cycle_graph(Graph, 3)
# 4 <- 1 -> 2 and 2 <- 3 -> 4
dispan = @acset Graph begin V=4; E=4; src= [1,1,3,3]; tgt=[2,4,2,4] end

#      e1
#    1 -> 2
# e2 |  / ^
#    vv   | e4
#    4 -> 3
#      e5
squarediag = Graph(4)
add_edges!(squarediag, [1,1,2,3,4],[2,4,4,2,3])

# Add a reverse arrow to span
span_w_arrow = Graph(3)
add_edges!(span_w_arrow,[1,1,2],[2,3,1])

L = ACSetTransformation(I2, arr, V=[1,2])
R = ACSetTransformation(I2, biarr, V=[1,2])
m = ACSetTransformation(arr, span, V=[2,1], E=[1])
@test is_isomorphic(span_w_arrow, rewrite_match(Rule(L, R), m; cat=Grph))

# Remove apex of a subspan (top left corner of squarediag, leaves the triangle behind)
L = ACSetTransformation(I2, span, V=[1,3])
m = ACSetTransformation(span, squarediag, V=[2,1,4], E=[1,2])
@test is_isomorphic(tri, rewrite_match(Rule(L,id[Grph](I2)), m; cat=Grph))

# Remove self-edge using a *non-monic* match morphism
two_loops = Graph(2)
add_edges!(two_loops,[1,2],[1,2]) # ↻1   2↺
one_loop = Graph(2)
add_edges!(one_loop,[2],[2]) # 1   2↺

L = ACSetTransformation(I2, arr, V=[1,2])
m = ACSetTransformation(arr, two_loops, V=[1, 1], E=[1])
@test is_isomorphic(one_loop, rewrite_match(Rule(L,id[Grph](I2)),m; cat=Grph))

# Non-discrete interface graph. Non-monic matching
arr_loop= @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,2] end  # 1->2↺
arrarr = @acset Graph begin V=2; E=2; src=[1,1]; tgt=[2,2] end #  1⇉2
arrarr_loop = @acset Graph begin V=2; E=3; src=[1,1,2]; tgt=[2,2,2] end # 1⇉2↺
arr_looploop = @acset Graph begin V=2;E=3; src= [1,2,2]; tgt=[2,2,2]end # 1-> ↻2↺

L = ACSetTransformation(arr, arr, V=[1,2],E=[1]) # identity
R = ACSetTransformation(arr, arrarr, V=[1,2], E=[1])
m = ACSetTransformation(arr, arr_loop, V=[2,2], E=[2]) # NOT MONIC
@test is_isomorphic(arr_looploop, rewrite_match(Rule(L,R),m; cat=Grph))

# only one monic match
@test is_isomorphic(arrarr_loop, rewrite(Rule(L, R; monic=true), arr_loop; cat=Grph))

# two possible morphisms L -> squarediag, but both violate dangling condition
L = ACSetTransformation(arr, span, V=[1,2], E=[1]);
m = ACSetTransformation(span, squarediag, V=[2,1,4], E=[1,2]);
@test (:src, 5, 4) in dangling_condition(ComposablePair(L,m))
@test_throws ErrorException Rule(L, id[Grph](arr)) # unnatural morphism

# violate id condition because two orphans map to same point
L = ACSetTransformation(I2, biarr, V=[1,2]); # delete both arrows
m = ACSetTransformation(biarr, arr_loop, V=[2,2], E=[2,2]);
@test (1, 2) in id_condition(L[:E], m[:E])[2]
L = ACSetTransformation(arr, biarr, V=[1,2], E=[1]); # delete one arrow
@test 1 in id_condition(L[:E],m[:E])[1]

span_triangle = @acset Graph begin V=3; E=3; src=[1,1,2];tgt= [2,3,3]end;# 2 <- 1 -> 3 (with edge 2->3)

L = ACSetTransformation(arr, tri, V=[1,2], E=[1]);
m = ACSetTransformation(tri, squarediag, V=[2,4,3], E=[3,5,4]);
@test is_isomorphic(span_triangle, rewrite_match(Rule(L,id[Grph](arr)),m; cat=Grph))

k, g = pushout_complement[Grph](ComposablePair(L, m)); # get PO complement to do further tests

# the graph interface is equal to the final graph b/c we only delete things
@test is_isomorphic(span_triangle, codom(k))

# Check pushout properties 1: apex is the original graph
@test is_isomorphic(squarediag, ob(pushout[Grph](L, k))) # recover original graph

# Check pushout properties 2: the diagram commutes
Lm = compose[Grph](L,m);
kg = compose[Grph](k,g);
for I_node in 1:2
  @test Lm[:V](I_node) == kg[:V](I_node)
end
@test Lm[:E](1) == kg[:E](1)

# Check pushout properties 3: for every pair of unmatched things between K and L, they are NOT equal
for K_node in 1:3
  @test m[:V](3) != g[:V](K_node)
end

for K_edge in 2:3
  @test m[:E](3) != g[:E](K_edge)
end


# Graphs with attributes
########################

@present SchDecGraph <: SchGraph begin
  X::AttrType
  dec::Attr(E,X)
end

@present SchLabeledDecGraph <: SchDecGraph begin
  label::Attr(V,X)
end

@acset_type LabeledDecGraph(SchLabeledDecGraph, index=[:src,:tgt]){String}

LGrph = ACSetCategory(VarACSetCat(LabeledDecGraph()))

aI2 = @acset LabeledDecGraph begin
  V = 2;  label = ["a","b"]
end

aarr = @acset LabeledDecGraph begin
  V=2;  E=1;  src=1; tgt=2
  dec = ["e1"];  label = ["a","b"]
end

abiarr = @acset LabeledDecGraph begin
  V = 2; E = 2; src = [1,2]; tgt = [2,1]
  dec = ["e1","rev_e1"]; label = ["a","b"]
end

aspan = @acset LabeledDecGraph begin
  V = 3; E = 2; src = [1,1];  tgt = [2,3]
  dec = ["e1","e2"];  label = ["a","b","c"]
end

expected = @acset LabeledDecGraph begin
  V = 3; E = 3; src = [1,1,2]; tgt = [2,3,1]
  dec = ["e1","e2","rev_e1"]
  label = ["a","b","c"]
end


L = ACSetTransformation(aI2, aarr, V=[1,2]; cat=LGrph);
R = ACSetTransformation(aI2, abiarr, V=[1,2]; cat=LGrph);
m = ACSetTransformation(aarr, aspan, V=[1,2], E=[1]; cat=LGrph);

@test is_isomorphic(expected, rewrite_match(Rule(L, R; cat=LGrph), m; cat=LGrph))

# Undirected bipartite graphs
#############################

𝒞BP = ACSetCategory(UndirectedBipartiteGraph())

# 1 --- 1
#    /
# 2 --- 2

z_ = @acset UndirectedBipartiteGraph begin
  V₁=2; V₂=2; E=3; src= [1,2,2]; tgt= [1,1,2]
end

line = @acset UndirectedBipartiteGraph begin 
  V₁=1; V₂=2; E=1; src=[1]; tgt=[1] 
end

parallel =  @acset UndirectedBipartiteGraph begin 
  V₁=2; V₂=2; E=2; src=[1,2]; tgt=[1,2] 
end

merge = @acset UndirectedBipartiteGraph begin 
  V₁=2; V₂=2; E=2; src=[1,2]; tgt=[1,1] 
end

Lspan =  @acset UndirectedBipartiteGraph begin 
  V₁=1; V₂=2; E=2; src=[1,1]; tgt=[1,2] 
end

I =  @acset UndirectedBipartiteGraph begin V₁=1; V₂=2; end

L = ACSetTransformation(I, Lspan, V₁=[1], V₂=[1,2])
R = ACSetTransformation(I, line, V₁=[1], V₂=[1,2])
m1 = ACSetTransformation(Lspan, z_, V₁=[1], V₂=[1,2], E=[1, 2])
m2 = ACSetTransformation(Lspan, z_, V₁=[1], V₂=[2,1], E=[2, 1])

@test is_isomorphic(parallel, rewrite_match(Rule(L, R), m1; cat=𝒞BP))
@test is_isomorphic(merge, rewrite_match(Rule(L, R), m2; cat=𝒞BP))


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

𝒞S = ACSetCategory(SSet())

quadrangle = @acset SSet begin
    T=2; E=5; V=4
    d1=[1,1]; d2=[2,3]; d3=[4,5]
    src=[1,1,1,2,3];  tgt=[4,2,3,4,4]
end

L = quadrangle  # We defined quadrilateral above.
I = @acset SSet begin
  E=4; V=4
  src=[1,1,2,3]
  tgt=[2,3,4,4]
end
R = @acset SSet begin
  T=2; E=5; V=4
  d1=[2,3]; d2=[1,5]; d3=[5,4]
  src=[1,1,2,3,2]; tgt=[2,3,4,4,3]
end
edge = @acset SSet begin E=1; V=2; src=[1]; tgt=[2] end
edge_left = only(homomorphisms(edge, L; initial=Dict([:V=>[1,3]])))
edge_left_R = only(homomorphisms(edge, R; initial=Dict([:V=>[1,3]])))
edge_right = only(homomorphisms(edge, L; initial=Dict([:V=>[2,4]])))
G = apex(pushout[𝒞S](edge_left, edge_right))
r = Rule(homomorphism(I, L; initial=(V=1:4,)), 
         homomorphism(I, R; initial=(V=1:4,));
         monic=true)
m = get_matches(r, G; cat=𝒞S)[1]
res =  rewrite_match(r, m; cat=𝒞S)
expected = apex(pushout[𝒞S](edge_left_R, edge_right))
@test !is_isomorphic(res, G) # it changed
@test is_isomorphic(res, expected)


# Rewriting Slices, not ACSets
##############################
two = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,1] end
L_ = path_graph(Graph, 2)
L = SliceOb(ACSetTransformation(L_, two, V=[2,1], E=[2]))
I_ = Graph(1)
I = SliceOb(ACSetTransformation(I_, two, V=[2]))
R_ = Graph(2)
R = SliceOb(ACSetTransformation(R_, two, V=[2, 1]))

𝒞2 = SliceC(Category(Grph), two)

rule = Rule(homomorphism(I, L; cat=Grph), homomorphism(I, R; cat=Grph); cat=𝒞2)
G_ = path_graph(Graph, 3)
G = SliceOb(ACSetTransformation(G_, two, V=[1,2,1], E=[1,2])) # (S) ⟶ [T] ⟶ (S)

H = rewrite(rule, G; cat=𝒞2)


# VARIABLES: Replace pair of parallel edges with one (sum weights)
#-----------------------------------------------------------------
𝒞WG = ACSetCategory(VarACSetCat(WeightedGraph{Int}()))

X = @acset WeightedGraph{Int} begin
  V=1; E=1; Weight=1; src=1; tgt=1; weight=[AttrVar(1)] 
end
rule = Rule(id[𝒞WG](WeightedGraph{Int}()), create[𝒞WG](X); cat=𝒞WG, freevar=true)
G = @acset WeightedGraph{Int} begin V=1; E=3; src=1; tgt=1; weight=[10,20,100] end
G2 = rewrite(rule, G; cat=𝒞WG)

L = @acset WeightedGraph{Int} begin V=2; E=2; Weight=2; src=1; tgt=2; 
                                    weight=AttrVar.(1:2) end
I = WeightedGraph{Int}(2)
R = @acset WeightedGraph{Int} begin V=2; E=1; Weight=1; src=1; tgt=2; 
                                    weight=[AttrVar(1)] end

l = homomorphism(I,L; initial=(V=1:2,), cat=𝒞WG)
r = homomorphism(I,R; initial=(V=1:2,), cat=𝒞WG)
rule = Rule(l, r; monic=[:E], expr=Dict(:Weight=>[xs->xs[1]+xs[2]]), cat=𝒞WG)

G = @acset WeightedGraph{Int} begin V=1; E=3; src=1; tgt=1; 
                                    weight=[10,20,100] end
m = get_matches(rule, G; cat=𝒞WG)[1]
@test rewrite_match(rule, m; cat=𝒞WG) == @acset WeightedGraph{Int} begin 
  V=1; E=2; src=1; tgt=1; weight=[30, 100] end

# or, introduce free variables 
rule = Rule(l, r; monic=[:E], freevar=true, cat=𝒞WG)
m = get_matches(rule, G; cat=𝒞WG)[1]
@test rewrite_match(rule, m; cat=𝒞WG) == @acset WeightedGraph{Int} begin 
  V=1; E=2; Weight=1; src=1; tgt=1; weight=[AttrVar(1), 100] end



# MAD Graphs
#############
@acset_type MGraph(SchGraph, part_type=BitSetParts) <: HasGraph
const M𝒞 = ACSetCategory(MADCSetCat(MGraph()))

m = CatWithCoequalizers(M𝒞)

G1 = MGraph(1)
i1 = id[M𝒞](G1)

r = Rule(i1, i1; cat=M𝒞)

rewrite(r, G1; cat=M𝒞)

end # module 
