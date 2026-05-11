module TestBenchmarkGeneration

using Test, AlgebraicRewriting, Catlab, nauty_jll
using AlgebraicRewriting.Incremental.BenchmarkGeneration: generate_benchmark
import AlgebraicRewriting

########################
# Directed Multigraphs #
########################
Q = path_graph(Graph, 3)
R = @acset Graph begin V=3; E=3; src=[1,1,2]; tgt=[2,3,3] end 
f = homomorphism(path_graph(Graph, 2), R; initial=(V=[1,3],))
ihs = IHS(Q, f, Graph());


generate_benchmark(ihs) # generates *and* runs the benchmark

########################
# Simplicial complexes #
########################

# TOO BIG OF AN EXAMPLE
# cannot enumerate the subobjects

# @present TriSchema <: SchGraph begin 
#   T::Ob
#   (t1,t2,t3)::Hom(T,V)
# end
# @test :V == AlgebraicRewriting.IHSData.distinguished_object(Schema(TriSchema))
# @acset_type Tri(TriSchema) <: AbstractSymmetricGraph

# Q = @acset Tri begin
#   V=6; E=8*2; T=2*6;
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
