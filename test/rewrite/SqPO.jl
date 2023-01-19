module TestSqPO 

using Test
using Catlab, Catlab.Graphs, Catlab.CategoricalAlgebra
using AlgebraicRewriting 
using AlgebraicRewriting.Rewrite.SqPO: final_pullback_complement

# Sesqui Pushout Tests
######################

# partial map classifier test
#############################
A = star_graph(Graph, 4)
X = path_graph(Graph, 2)
B = @acset Graph begin V = 1; E = 1; src=[1]; tgt=[1] end
m = CSetTransformation(X,A,V=[4,1],E=[1])
f = CSetTransformation(X,B,V=[1,1],E=[1])
phi = partial_map_classifier_universal_property(m,f)

# check pullback property
m_, f_ = pullback(phi, partial_map_classifier_eta(B)).cone

# This is isomorphic, but it's a particular implementation detail which
# isomorphism is produced. At the time of writing this test, it turns out we get
# an identical span if we reverse the arrow of the apex X
iso = CSetTransformation(X,X;V=[2,1], E=[1])
@test force(compose(iso, m_)) == m
@test force(compose(iso, f_)) == f

# Another test
#------------
loop = @acset Graph begin
  V=1; E=1; src=[1]; tgt=[1] end
fromLoop = @acset Graph begin
  V=2; E=2; src=[1,1]; tgt=[2,1] end
toLoop = @acset Graph begin
  V=2; E=2; src=[1,2]; tgt=[2,2] end
f = CSetTransformation(loop, fromLoop, V=[1],E=[2])
m = CSetTransformation(loop, toLoop, V=[2],E=[2])
u = partial_map_classifier_universal_property(m,f)
m_,f_ = pullback(u, partial_map_classifier_eta(codom(f))).cone
@test force.([m_,f_]) == [m,f]


# Final pullback complement test
################################
A, B, C = Graph(2), Graph(1), path_graph(Graph, 2)
f = CSetTransformation(A,B;V=[1,1])
m = CSetTransformation(B,C; V=[2])

fpc = final_pullback_complement(ComposablePair(f,m))

# Sesqui-pushout rewriting
###########################
# Examples from Corradini (2006) access control model

# (Figure 3) Clone a node that points to other things
# resulting in the copies both sharing what they point to
#----------------------------------------------------------
L, I, R = Graph.([1,2,2])
G = @acset Graph begin V=3; E=2; src=1; tgt=[2,3] end
m = CSetTransformation(L, G; V=[1])
l = CSetTransformation(I, L; V=[1,1])
r = id(I)

rw = rewrite_match(Rule{:SqPO}(l, r), m)
@test is_isomorphic(rw, @acset Graph begin
  V=4; E=4; src=[1,1,2,2]; tgt=[3,4,3,4] end)

# (Figure 2) Another example that's nondeterministic for DPO
# category of simple graphs is quasi-adhesive, and uniqueness of
# pushout complements is guaranteed along regular monos only, i.e., morphisms
# reflecting edges: but this l morphism is not regular.
L, I, R = path_graph(Graph, 2), Graph(2), Graph(2)
G = @acset Graph begin V=3; E=3; src=1; tgt=[2,2,3] end
l, r = CSetTransformation(I, L; V=[1,2]), id(I)
m = CSetTransformation(L, G; V=[1,2], E=[1])
rw = rewrite_match(Rule{:SqPO}(l,r), m)
@test is_isomorphic(rw, @acset Graph begin V=3; E=2; src=1; tgt=[2,3] end)

# (Figure 1) Example that would be dangling condition violation for DPO
# However, SqPO deletes greedily
G= @acset Graph begin V=4; E=3; src=[1,3,3]; tgt=[2,2,4] end
L,I,R = Graph.([1,0,0])
l, r = CSetTransformation(I,L), CSetTransformation(I,R)
m = CSetTransformation(L, G; V=[3])
rw = rewrite_match(Rule{:SqPO}(l,r), m)
@test is_isomorphic(rw, @acset Graph begin V=3; E=1; src=1; tgt=2 end)


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

Tri = @acset SSet begin
  T=1; E=3; V=3;
  d1=[1]; d2=[2]; d3=[3];
  src=[1,1,2]; tgt=[3,2,3]
end

L = @acset SSet begin V=1 end
I = @acset SSet begin V=2 end
r =Rule{:SqPO}(homomorphism(I,L),id(I))
m = CSetTransformation(L, Tri, V=[1]);
# We get 4 'triangles' when we ignore equations
@test nparts(rewrite_match(r, m), :T) == 4

resSqPO= rewrite_match(r, m; pres=ThSemisimplicialSet) # pass in the equations
@test nparts(resSqPO, :T) == 2 # the right number of triangles

end # module 
