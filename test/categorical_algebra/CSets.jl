module TestCSets
using Test
using Catlab, Catlab.Graphs, Catlab.CategoricalAlgebra
using AlgebraicRewriting


# Pushout complement 
####################

# Simplest non-trivial, non-monic exmaple
@present TheoryFinSet(FreeSchema) begin
  X::Ob
end
@acset_type FinSetType(TheoryFinSet)

I, L, G = [@acset FinSetType begin X=i end for i in [2,1,1]]
l = ACSetTransformation(I, L, X=[1,1])
m = ACSetTransformation(L, G, X=[1])
@test can_pushout_complement(ComposablePair(l,m))
ik, kg = pushout_complement(ComposablePair(l,m))
# There are 3 functions `ik` that make this a valid P.C.
# codom=1 with [1,1], codom=2 with [1,2] or [2,1]
K = codom(ik)
@test nparts(K, :X) == 1 # algorithm currently picks the first option

@present TheoryLFinSet(FreeSchema) begin
  X::Ob; D::AttrType; f::Attr(X,D)
end
@acset_type LFinSetType(TheoryLFinSet)
const LSet = LFinSetType{Symbol}

I = @acset LSet begin X=1; D=1; f=[AttrVar(1)] end
G = @acset LSet begin X=2; f=[:x,:y] end
f = homomorphism(I,G)

kg = last(pushout_complement(id(I),f))
@test dom(kg) == @acset LSet begin X=2; D=1; f=[AttrVar(1),:y] end
@test collect(kg[:D]) == [:x]

# Slices 
########
two = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,1] end

L_ = path_graph(Graph, 2)
L = Slice(ACSetTransformation(L_, two, V=[2,1], E=[2]))

G_ = path_graph(Graph, 3)
G = Slice(ACSetTransformation(G_, two, V=[1,2,1], E=[1,2]))

@test length(homomorphisms(L_, G_)) == 2
@test length(homomorphisms(L, G)) == 1

# Extending morphisms
#####################
# TODO

# Postcomposing morphisms
#########################
# TODO 

# Inverting morphisms
#####################
# TODO 

# Checking pullback up to iso
#############################
# TODO 

# Substituting variables
########################

# Abstraction
##############
# TODO 

# Var pullback 
##############

const WG = WeightedGraph{Bool}

C = @acset WG begin V=1; Weight=1; E=2; src=1;tgt=1;weight=[true, AttrVar(1)] end 
A = @acset WG begin V=1; Weight=2; E=3; src=1;tgt=1;
                    weight=[true, AttrVar.(1:2)...] end
f = homomorphism(A,C; initial=(E=[1,1,2],))
var_pullback(Cospan(f,f))

end # module
