module TestSchedules

using Test
using Catlab, Catlab.Graphs, Catlab.CategoricalAlgebra
using AlgebraicRewriting
using AlgebraicRewriting.Schedules: RWStep

const hom = Catlab.CategoricalAlgebra.homomorphism

G0,G1,G2,G3 = Graph.([0,1,2,3])
# Delete a node
Rule1 = Span(create(G1), id(G0));
# Merge two nodes
Rule2 = Span(id(G2), hom(G2, G1));
# Add a node
Rule3 = Span(id(G0), create(G1))

R1,R2,R3 = [Rule(l,r) for (l,r) in [Rule1,Rule2,Rule3]]

### Trajectory

# step 1: add node #3 to G2
M1 = create(G2)
CM1 = ACSetTransformation(G1, G3; V=[3])
Pmap1 = Span(id(G2), ACSetTransformation(G2, G3; V=[1,2]))
RS1 = RWStep(Rule3, Pmap1, M1, CM1)

# Step 2: merge node 2 and 3 to yield a G2
M2 = ACSetTransformation(G2, G3; V=[2,3])
CM2 = ACSetTransformation(G1, G2; V=[2])
Pmap2 = Span(id(G3), ACSetTransformation(G3, G2; V=[1,2,2]))
RS2 = RWStep(Rule2, Pmap2, M2, CM2)

# Step 3: delete vertex 1 
M3 = ACSetTransformation(G1, G2; V=[1])
CM3 = create(G1)
Pmap3 = Span(ACSetTransformation(G1,G2; V=[2]), id(G1))
RS3 = RWStep(Rule1, Pmap3, M3, CM3)


steps = [RS1, RS2, RS3]

g = find_deps(steps)
expected = @acset Graph begin V=3; E=1; src=1; tgt=2 end
@test expected == g

# Interface that just uses rules and match morphisms:
# The matches needed to be updated to reflect the particular isomorph that DPO
# rewriting produces when applying the rule.
σ₂ = ACSetTransformation(G2,G2;V=[2,1])
σ₃ = ACSetTransformation(G3,G3;V=[3,1,2])

g′ = find_deps([R3=>M1, R2=>M2⋅σ₃, R1=>M3⋅σ₂])
@test g′ == g

end # module
