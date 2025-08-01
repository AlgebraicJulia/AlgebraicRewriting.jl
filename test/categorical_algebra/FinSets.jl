module TestFinSets
using Test
using Catlab, Catlab.Theories
using AlgebraicRewriting

𝒞 = SkelFinSet()
# Pushout complements
#--------------------

f = FinFunction([1,3], 4)
g = FinFunction([1,2,5,6], 6)
@test can_pushout_complement[𝒞](f, g)
h, k = pushout_complement[𝒞](f, g)
@test force(compose[𝒞](f,g)) == force(compose[𝒞](h,k))
colim = pushout[𝒞](f,h)
@test ob(colim) == FinSetInt(6)
@test allunique(collect(pushout_copair[𝒞](colim, g, k)))

universal[𝒞](colim, Cospan(g, k))

# Identification condition failure.
f = FinFunction([1,3], 4)
g = FinFunction([1,2,2,3], 3)

@test !can_pushout_complement[𝒞](f, g)
@test_throws ErrorException pushout_complement[𝒞](f, g)


end # module