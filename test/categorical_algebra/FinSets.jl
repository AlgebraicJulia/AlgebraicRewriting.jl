module TestFinSets
using Test
using Catlab, Catlab.Theories
using Catlab.CategoricalAlgebra: FinFunction, FinSet, pushout
using AlgebraicRewriting


# Pushout complements
#--------------------

f = FinFunction([1,3], 4)
g = FinFunction([1,2,5,6], 6)
@test can_pushout_complement(f, g)
h, k = pushout_complement(f, g)
@test f⋅g == h⋅k
colim = pushout(f,h)
@test ob(colim) == FinSet(6)
@test allunique(collect(copair(colim, g, k)))

# Identification condition failure.
f = FinFunction([1,3], 4)
g = FinFunction([1,2,2,3], 3)
@test !can_pushout_complement(f, g)
@test_throws ErrorException pushout_complement(f, g)


end # module