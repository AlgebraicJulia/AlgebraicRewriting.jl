module TestIncrementalCC 

using Test
using AlgebraicRewriting, Catlab
using AlgebraicRewriting.Incremental.IncrementalCC: IncCCHomSet, match_vect
using AlgebraicRewriting.Incremental.IncrementalSum: IncSumHomSet
using AlgebraicRewriting.Incremental.IncrementalHom: state, deletion!, addition!

# Graph incremental hom search
#-----------------------------
T = ob(terminal(Graph))
                                                                  #  • ⇉ •
e, ee = path_graph.(Graph, 2:3)                                   #   ↘ ↙
A = @acset Graph begin V=3; E=4; src=[1,1,1,2]; tgt=[2,2,3,3] end #    •
A_rule = Rule(id(e), homomorphism(e, A));

# Empty edge case
#----------------
hset = IncHomSet(Graph(), [A_rule.R], Graph(3)); 
@test length(matches(hset)) == 1
@test only(keys(hset)) == (1=>1)
@test hset[1] == hset[1=>1]

# Single connected component pattern
#----------------
start = @acset Graph begin V=3; E=3; src=[1,2,3]; tgt=[2,3,3] end
hset = IncHomSet(ee, [A_rule.R], start);
@test length.(match_vect(hset)) == [3]

m = homomorphisms(e, start)[2]
del, add = rewrite!(hset, A_rule, m)
@test isempty(del)
@test length(add) == 6
@test length.(match_vect(hset)) == [3,0,6]
@test validate(hset)

m = homomorphism(e, state(hset); monic=true)
rewrite!(hset, A_rule)
@test validate(hset)
@test length.(match_vect(hset)) == [3, 0, 6, 0, 8]
@test !haskey(hset, 3=>7)
@test haskey(hset, 5=>7)
@test hset[5=>8] == hset[17]

@test hset == IncCCHomSet(hset)
roundtrip = IncCCHomSet(IncSumHomSet(hset));
@test roundtrip isa IncCCHomSet
@test length.(match_vect(roundtrip)) == [17]


# Blog example
#----------------
tri = @acset Graph begin V=3;E=3;src=[1,1,2];tgt=[3,2,3]end
X = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,2] end
omap = homomorphism(e, X)
hset = IncHomSet(ee, [homomorphism(e, tri)], X);
addition!(hset, 1, omap)
@test validate(hset)


# Monic contraints
#----------------
mset = IncHomSet(Graph(2), [create(Graph(1))], Graph(2); monic=true);
@test mset isa IncCCHomSet
@test length(matches(mset)) == 2
M_rule = Rule(id(Graph()), create(Graph(1)); monic=true)
rewrite!(mset, M_rule)
@test length.(match_vect(mset)) == [2, 0, 4]

# Application conditions: NAC removing morphisms during addition!
#----------------
del = delete(Graph(1))
AlgebraicRewriting.Incremental.Constraints.NAC(del)
mset = IncHomSet(Graph(1), [del], Graph(2)⊕T; nac=[del]);
@test length(keys(mset)) == 2
M_rule = Rule(id(Graph(1)), delete(Graph(1)); ac=[AppCond(del, false)])
rewrite!(mset, M_rule)
@test length(keys(mset)) == 1
rewrite!(mset, M_rule)
@test length(keys(mset)) == 0
@test isnothing(rewrite!(mset, M_rule))

# Application conditions: NAC adding morphisms during deletion!
#--------------------------------------------------------------
del = homomorphism(⊕(Graph[fill(T, 2); Graph(1)]), 
                   state(mset); monic=true) # delete one loop
deletion!(mset, del)
@test length(keys(mset)) == 1
del = homomorphism(⊕(Graph[T; Graph(2)]), 
                   state(mset); monic=true) # delete another loop
deletion!(mset, del)
@test length(keys(mset)) == 2

del = homomorphism(Graph(3), state(mset); monic=true) # delete another loop
deletion!(mset, del)
@test length(keys(mset)) == 3

# NAC with DPO optimization
#--------------------------
edge_loop = @acset Graph begin V=2; E=2; src=[1,1]; tgt=[1,2] end
# rem edge, not if src has loop
r = Rule(homomorphism(Graph(2), e; monic=true), id(Graph(2));
         ac=[AppCond(homomorphism(e, edge_loop; monic=true), false; monic=true)])

mset = IncHomSet(r, edge_loop);
# @test length(keys(mset)) == 1
rewrite!(mset, r)
@test length(keys(mset)) == 1
rewrite!(mset, r)
@test length(keys(mset)) == 0

# Weighted Graph
#---------------
if false 
  const WG′ = WeightedGraph{Bool}
e, ee = path_graph.(WG′, 2:3)
e[:weight] = [AttrVar(add_part!(e, :Weight))]
ee[:weight] = [true, AttrVar(add_part!(ee, :Weight))]
A = @acset WG′ begin V=3; E=4; Weight=1; 
  src=[1,1,1,2]; tgt=[2,2,3,3]; weight=[AttrVar(1), true, false, true] 
end
A_rule = Rule(id(e), homomorphism(e, A))

start = @acset WG′ begin V=3; E=3; src=[1,2,3]; tgt=[2,3,3]; weight=Bool[0,1,0] end
init_match = homomorphisms(e, start)[2]

#               ⊤  [1]                ⊥   ⊤   
# Pattern :   • → • → •   ||| Start: • → • → • ↺ ⊥   (there is only one map)

#            [1]        [1],⊤  
# Addition: • → •   => •  ⇉  •
#                     ⊥ ↘  ↙ ⊤
#                         •

# Result of applying the addition to the ⊤ edge of `Start` (there are two maps)
#                    ⊥  ⊤,⊤   
#                  • → • ⇉ • ↺ ⊥
#                     ⊥ ↘ ↙ ⊤
#                        •
hset = IncHomSet(ee, [A_rule.R], start);
rewrite!(hset, A_rule, init_match)
@test validate(hset)
expected = @acset WeightedGraph{Bool} begin 
  V=4; E=6; src=[1,2,2,2,3,3]; tgt=[2,3,3,4,3,4]; weight=Bool[0,1,1,0,0,1]
end
@test is_isomorphic(expected, state(hset))

m = error("TO DO: get the monic match we were getting before")
rewrite!(hset, A_rule)
@test validate(hset)


## DDS 
#-----
@present SchDDS(FreeSchema) begin X::Ob; Φ::Hom(X,X) end
@acset_type DDS(SchDDS, index=[:Φ])
DDS(i::Int) = @acset DDS begin X=i; Φ=[rand(1:i) for _ in 1:i] end
DDS(phi::Vector{Int}) = @acset DDS begin X=(length(phi)); Φ=phi end

p2 = DDS([2,2])
p22 = p2 ⊕ p2
r = homomorphism(p22, DDS([2,2,4,4,4]); monic=true)
hset = IncHomSet(p22, [r], p22);
rewrite!(hset, Rule(id(p22), r), id(p22))
@test validate(hset)

I = DDS([1,2,1])
r = ACSetTransformation(I, DDS([1,2,1,1]); X=[1, 2, 3])
start = DDS([1])
m = homomorphism(I, start)
hset = IncHomSet(DDS([1,1,1]), [r], start);
rewrite!(hset, Rule(id(I), r), m)
@test validate(hset)
end
end # module
