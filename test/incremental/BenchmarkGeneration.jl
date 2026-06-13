module TestBenchmarkGeneration

using Test, AlgebraicRewriting, Catlab, nauty_jll
using AlgebraicRewriting.Incremental.BenchmarkGeneration: generate_benchmark
import AlgebraicRewriting

########################
# Directed Multigraphs #
########################
grph(x) = to_graphviz(x; node_labels=true, edge_labels=true)

# Q = x → y → z = 2 edge path
# L = 1 → 3     = 1 edge
# R = {1 → 3, 1 → 2, 2 → 3} = makes L into an acyclic triangle by adding apex 2
Q = path_graph(Graph, 3);
R = @acset Graph begin V=3; E=3; src=[1,1,2]; tgt=[2,3,3] end;
f = homomorphism(path_graph(Graph, 2), R; initial=(V=[1,3],));
ihs = IHS(Q, f, Graph());
AlgebraicRewriting.Incremental.IHSAccess.check_interactions(ihs)
get_cases(ihs)

generate_benchmark(ihs; N_REWRITES=8_000_000, runbenchmark=false)

###################
# Trivial example #
###################
# Q = {1 → 2, 2 → 3, 3 → 1} = cyclic triangle
# L = 1 → 3                 = edge
# R = {1 → 2, 1 → 3, 3 → 2} = acyclic triangle by adding arrows into new apex 3
# (100% speedup because this rewrite cannot create a cyclic triangle)
Q = cycle_graph(Graph, 3)
R = @acset Graph begin V=3; E=3; src=[1,1,3]; tgt=[2,3,2] end 
f = homomorphism(path_graph(Graph, 2), R; initial=(V=[1,3],))
ihs = IHS(Q, f, Graph());

generate_benchmark(ihs; N_TRIALS=3, runbenchmark=false)

#######
# AST #
#######

"""
Represent ASTs with Plus and Times. p1 (resp. t1) is the output of the
operation, p2 and p3 are the inputs.
"""
@present SchAST(FreeSchema) begin 
  (V,P,T)::Ob
  (p1,p2,p3)::Hom(P,V)
  (t1,t2,t3)::Hom(T,V)
end

@acset_type AST(SchAST)

# Let 1..5 be {a,b,x,y,z}. Then this query is asking for left associated 
# additions, i.e. {add(a,b,z),add(b,x,y)}
Q = @acset AST begin
  V=5; P=2; 
  p1=[2,1]
  p2=[3,2]
  p3=[4,5]
end;

# Let 1..5 be {a,b,x,y,z}. Pattern is a=(x+y)*z
L = @acset AST begin 
  V=5; P=1;T=1 
  p1=[2]; t1=[1]
  p2=[3]; t2=[2]
  p3=[4]; t3=[5]
end;

# Extend L with the fact that a=(x*z)+(y*z)
R = @acset AST begin
  V=7; P=2;T=3 
  p1=[2,1];  t1=[1,6,7]
  p2=[3,6];  t2=[2,3,4]
  p3=[4,7];  t3=[5,5,5]
end;

f = homomorphism(L, R; initial=(V=1:5,));
ihs = IHS(Q, f, AST()); # 2 min
cases = get_cases(ihs; batch=true, quotient=true) # 3 min
generate_benchmark(ihs; cases, runbenchmark=false) # generates *and* runs the benchmark


########################
# Simplicial complexes #
########################

# TOO BIG OF AN EXAMPLE
# cannot even enumerate the subobjects

# @present TriSchema <: SchGraph begin 
#   T::Ob
#   (t1,t2,t3)::Hom(T,V)
# end
# @test :V == AlgebraicRewriting.IHSData.distinguished_object(Schema(TriSchema))
# @acset_type Tri(TriSchema) <: AbstractSymmetricGraph

# Q = @acset Tri begin
#   V=6; E;
#   src=[1,1,1,1,1,2,4,5, 2,3,4,5,6,3,5,6]
#   tgt=[2,3,4,5,6,3,5,6, 1,1,1,1,1,2,4,5]
#   t1=[1,2,3,1,2,3, 1,5,6,1,5,6]
#   t2=[2,3,1,3,1,2, 5,6,1,6,1,5]
#   t3=[3,1,2,2,3,1, 6,1,5,6,6,1]
# end

# R = @acset Tri begin
#   V=6; E=7*2; T=2*6;
#   src=[1,1,1,1,2,4,5, 2,3,5,6,3,5,6]; 
#   tgt=[2,3,5,6,3,5,6, 1,1,1,1,2,4,5];
#   t1=[1,2,3,1,2,3, 1,5,6,1,5,6]
#   t2=[2,3,1,3,1,2, 5,6,1,6,1,5]
#   t3=[3,1,2,2,3,1, 6,1,5,6,6,1]
# end 

# f = ACSetTransformation(Tri(3), R; V=[1,4,6])
# ihs = IHS(Q, f, Tri());

# generate_benchmark(ihs)

end # module
