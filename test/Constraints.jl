using AlgebraicRewriting
using Catlab.CategoricalAlgebra, Catlab.Graphs
using Test 

"""
Positive application condition: a particular matched vertex must have self loop.

  [↻•⟶•] ⟵ [•⟶•]
      ∃↘    ↓ ?
        [ ? ]

"""
looparr = @acset Graph begin V=2; E=2; src=[1,1]; tgt=[1,2] end 
p2 = path_graph(Graph, 2)
f=homomorphism(p2,looparr; monic=true)
constr = AppCond(f, true)

G = @acset Graph begin V=1;E=1;src=1;tgt=1 end
f = homomorphism(p2, G)

@test apply_constraint(constr, f)
@test !apply_constraint(constr, id(p2))


"""
         ∀ 
  [↻•]   →  ?
    ↓    ↗ ∃ ↓ 
  [↻•⟶•]  → [↻•⟶•⟵•↺]

Every vertex with a loop also has a map to the vertex marked by the bottom map.
"""
t = terminal(Graph)|>apex
v = homomorphism(t, looparr)
loop_csp = @acset Graph begin V=3;E=4; src=[1,3,1,3]; tgt=[1,3,2,2] end 
b = homomorphism(looparr, loop_csp; monic=true)
constr = LiftCond(v, b)

@test !apply_constraint(constr,homomorphism(t, loop_csp))
@test apply_constraint(constr,b)


"""
        ∀ 
   [•]  →  ?
    ↓   ↗∃ ↓ 
  [•⟶•] ↪ [↻•⟶•⟵•↺]


Every vertex mapped into the leftmost vertex must also have an outgoing edge to
a vertex that is is mapped into the middle vertex.
"""

constr = LiftCond(homomorphism(Graph(1),p2), 
                  homomorphism(p2, loop_csp; monic=true))

G = @acset Graph begin V=3; E=3; src=[1,1,3]; tgt=[1,2,3] end 
h1,h2,h3,h4 = homomorphisms(G, loop_csp; initial=(V=Dict(1=>1),))
# h1,h2: we send V2 ↦ V1 (else: ↦2) Violates lift condition for the map into V=1
# h1,h3: we send V3 ↦ V1 (else: ↦3) Violates lift condition for the map into V=3

@test !apply_constraint(constr,h1)
@test !apply_constraint(constr,h2)
@test !apply_constraint(constr,h3)
@test apply_constraint(constr,h4)
