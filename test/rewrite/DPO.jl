module TestDPO 

using Test
using Catlab, Catlab.CategoricalAlgebra, Catlab.Programs, Catlab.Graphs
using AlgebraicRewriting

# Graphs
########

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
@test is_isomorphic(span_w_arrow, rewrite_match(Rule(L, R), m))

# Remove apex of a subspan (top left corner of squarediag, leaves the triangle behind)
L = ACSetTransformation(I2, span, V=[1,3])
m = ACSetTransformation(span, squarediag, V=[2,1,4], E=[1,2])
@test is_isomorphic(tri, rewrite_match(Rule(L,id(I2)),m))

# Remove self-edge using a *non-monic* match morphism
two_loops = Graph(2)
add_edges!(two_loops,[1,2],[1,2]) # ↻1   2↺
one_loop = Graph(2)
add_edges!(one_loop,[2],[2]) # 1   2↺

L = ACSetTransformation(I2, arr, V=[1,2])
m = ACSetTransformation(arr, two_loops, V=[1, 1], E=[1])
@test is_isomorphic(one_loop, rewrite_match(Rule(L,id(I2)),m))

# Non-discrete interface graph. Non-monic matching
arr_loop= @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,2] end  # 1->2↺
arrarr = @acset Graph begin V=2; E=2; src=[1,1]; tgt=[2,2] end #  1⇉2
arrarr_loop = @acset Graph begin V=2; E=3; src=[1,1,2]; tgt=[2,2,2] end # 1⇉2↺
arr_looploop = @acset Graph begin V=2;E=3; src= [1,2,2]; tgt=[2,2,2]end # 1-> ↻2↺

L = ACSetTransformation(arr, arr, V=[1,2],E=[1]) # identity
R = ACSetTransformation(arr, arrarr, V=[1,2], E=[1])
m = ACSetTransformation(arr, arr_loop, V=[2,2], E=[2]) # NOT MONIC
@test is_isomorphic(arr_looploop, rewrite_match(Rule(L,R),m))

# only one monic match
@test is_isomorphic(arrarr_loop, rewrite(Rule(L, R; monic=true), arr_loop))

# two possible morphisms L -> squarediag, but both violate dangling condition
L = ACSetTransformation(arr, span, V=[1,2], E=[1]);
m = ACSetTransformation(span, squarediag, V=[2,1,4], E=[1,2]);
@test (:src, 5, 4) in dangling_condition(ComposablePair(L,m))
@test_throws ErrorException Rule(L, id(arr)) # unnatural morphism

# violate id condition because two orphans map to same point
L = ACSetTransformation(I2, biarr, V=[1,2]); # delete both arrows
m = ACSetTransformation(biarr, arr_loop, V=[2,2], E=[2,2]);
@test (1, 2) in id_condition(ComposablePair(L[:E],m[:E]))[2]
L = ACSetTransformation(arr, biarr, V=[1,2], E=[1]); # delete one arrow
@test 1 in id_condition(ComposablePair(L[:E],m[:E]))[1]

span_triangle = @acset Graph begin V=3; E=3; src=[1,1,2];tgt= [2,3,3]end;# 2 <- 1 -> 3 (with edge 2->3)

L = ACSetTransformation(arr, tri, V=[1,2], E=[1]);
m = ACSetTransformation(tri, squarediag, V=[2,4,3], E=[3,5,4]);
@test is_isomorphic(span_triangle, rewrite_match(Rule(L,id(arr)),m))

k, g = pushout_complement(ComposablePair(L, m)); # get PO complement to do further tests

# the graph interface is equal to the final graph b/c we only delete things
@test is_isomorphic(span_triangle, codom(k))

# Check pushout properties 1: apex is the original graph
@test is_isomorphic(squarediag, ob(pushout(L, k))) # recover original graph

# Check pushout properties 2: the diagram commutes
Lm = compose(L,m);
kg = compose(k,g);
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

@acset_type LabeledDecGraph(SchLabeledDecGraph, index=[:src,:tgt])

aI2 = @acset LabeledDecGraph{String} begin
  V = 2;  label = ["a","b"]
end

aarr = @acset LabeledDecGraph{String} begin
  V=2;  E=1;  src=1; tgt=2
  dec = ["e1"];  label = ["a","b"]
end

abiarr = @acset LabeledDecGraph{String} begin
  V = 2; E = 2; src = [1,2]; tgt = [2,1]
  dec = ["e1","rev_e1"]; label = ["a","b"]
end

aspan = @acset LabeledDecGraph{String} begin
  V = 3; E = 2; src = [1,1];  tgt = [2,3]
  dec = ["e1","e2"];  label = ["a","b","c"]
end

expected = @acset LabeledDecGraph{String} begin
  V = 3
  E = 3
  src = [1,1,2]
  tgt = [2,3,1]
  dec = ["e1","e2","rev_e1"]
  label = ["a","b","c"]
end


L = ACSetTransformation(aI2, aarr, V=[1,2]);
R = ACSetTransformation(aI2, abiarr, V=[1,2]);
m = ACSetTransformation(aarr, aspan, V=[1,2], E=[1]);

@test is_isomorphic(expected, rewrite_match(Rule(L, R), m))

# Undirected bipartite graphs
#############################

# 1 --- 1
#    /
# 2 --- 2

z_ = @acset UndirectedBipartiteGraph begin
  V₁=2; V₂=2; E=3; src= [1,2,2]; tgt= [1,1,2]
end

line = UndirectedBipartiteGraph()
add_vertices₁!(line, 1)
add_vertices₂!(line, 2)
add_edges!(line, [1], [1])

parallel = UndirectedBipartiteGraph()
add_vertices₁!(parallel, 2)
add_vertices₂!(parallel, 2)
add_edges!(parallel, [1,2], [1,2])

merge = UndirectedBipartiteGraph()
add_vertices₁!(merge, 2)
add_vertices₂!(merge, 2)
add_edges!(merge, [1,2], [1,1])

Lspan = UndirectedBipartiteGraph()
add_vertices₁!(Lspan, 1)
add_vertices₂!(Lspan, 2)
add_edges!(Lspan, [1,1],[1,2])

I = UndirectedBipartiteGraph()
add_vertices₁!(I, 1)
add_vertices₂!(I, 2)

L = ACSetTransformation(I, Lspan, V₁=[1], V₂=[1,2])
R = ACSetTransformation(I, line, V₁=[1], V₂=[1,2])
m1 = ACSetTransformation(Lspan, z_, V₁=[1], V₂=[1,2], E=[1, 2])
m2 = ACSetTransformation(Lspan, z_, V₁=[1], V₂=[2,1], E=[2, 1])

@test is_isomorphic(parallel, rewrite_match(Rule(L, R), m1))
@test is_isomorphic(merge, rewrite_match(Rule(L, R), m2))


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
edge_left = homomorphism(edge, L; initial=Dict([:V=>[1,3]]))
edge_left_R = homomorphism(edge, R; initial=Dict([:V=>[1,3]]))
edge_right = homomorphism(edge, L; initial=Dict([:V=>[2,4]]))
G = apex(pushout(edge_left, edge_right))
r = Rule(homomorphism(I, L; monic=true), homomorphism(I, R; monic=true);
         monic=true)
res =  rewrite(r, G)
expected = apex(pushout(edge_left_R, edge_right))
@test !is_isomorphic(res, G) # it changed
@test is_isomorphic(res, expected)


# Rewriting Slices, not ACSets
##############################
two = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,1] end
L_ = path_graph(Graph, 2)
L = Slice(ACSetTransformation(L_, two, V=[2,1], E=[2]))
I_ = Graph(1)
I = Slice(ACSetTransformation(I_, two, V=[2]))
R_ = Graph(2)
R = Slice(ACSetTransformation(R_, two, V=[2, 1]))

rule = Rule(homomorphism(I, L), homomorphism(I, R))
G_ = path_graph(Graph, 3)
G = Slice(ACSetTransformation(G_, two, V=[1,2,1], E=[1,2])) # (S) ⟶ [T] ⟶ (S)

H = rewrite(rule, G)


# VARIABLES: Replace pair of parallel edges with one (sum weights)
#-----------------------------------------------------------------
X = @acset WeightedGraph{Int} begin 
  V=1; E=1; Weight=1; src=1; tgt=1; weight=[AttrVar(1)] 
end
rule = Rule(id(WeightedGraph{Int}()), create(X); freevar=true)
G = @acset WeightedGraph{Int} begin V=1; E=3; src=1; tgt=1; weight=[10,20,100] end
G2 = rewrite(rule,G)

L = @acset WeightedGraph{Int} begin V=2; E=2; Weight=2; src=1; tgt=2; 
                                    weight=AttrVar.(1:2) end
I = WeightedGraph{Int}(2)
R = @acset WeightedGraph{Int} begin V=2; E=1; Weight=1; src=1; tgt=2; 
                                    weight=[AttrVar(1)] end

l = homomorphism(I,L; monic=true)
r = homomorphism(I,R; monic=true)
rule = Rule(l, r; monic=[:E], expr=Dict(:Weight=>[xs->xs[1]+xs[2]]))

G = @acset WeightedGraph{Int} begin V=1; E=3; src=1; tgt=1; 
                                    weight=[10,20,100] end

@test rewrite(rule, G) == @acset WeightedGraph{Int} begin 
  V=1; E=2; src=1; tgt=1; weight=[30, 100] end

# or, introduce free variables 
rule = Rule(l, r; monic=[:E], freevar=true)
@test rewrite(rule, G) == @acset WeightedGraph{Int} begin 
  V=1; E=2; Weight=1; src=1; tgt=1; weight=[AttrVar(1), 100] end

# Rewriting with induced equations between AttrVars in the rule
#--------------------------------------------------------------
@present SchFoo(FreeSchema) begin X::Ob; D::AttrType; f::Attr(X,D) end
@acset_type AbsFoo(SchFoo)
const Foo = AbsFoo{Bool}

L = @acset Foo begin X=2; f=[false, false] end 
I = @acset Foo begin X=2;D=2; f=AttrVar.(1:2) end 
R = @acset Foo begin X=2; f=[false, true]end 
rule = Rule(homomorphism(I, L; monic=[:X]), homomorphism(I, R; monic=[:X]))

# we cannot match both X of L to the same part in G because this would yield 
# an inconsistent result
@test length(get_matches(rule, L)) == 2

res = rewrite(rule, L)
@test is_isomorphic(res, R)

end # module 
