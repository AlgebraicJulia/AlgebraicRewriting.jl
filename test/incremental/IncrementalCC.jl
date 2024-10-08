module TestIncrementalCC 

using Test
using AlgebraicRewriting, Catlab
using AlgebraicRewriting.Incremental.IncrementalCC: IncCCHomSet, match_vect
using AlgebraicRewriting.Incremental.IncrementalSum: IncSumHomSet
using AlgebraicRewriting.Incremental.IncrementalHom: state, deletion!, addition!

# Graph incremental hom search
#-----------------------------
T = ob(terminal(Graph))
G2 = Graph(2)
                                                                  #  • ⇉ •
e, ee = path_graph.(Graph, 2:3)                                   #   ↘ ↙
A = @acset Graph begin V=3; E=4; src=[1,1,1,2]; tgt=[2,2,3,3] end #    •
A_rule = Rule(id(e), homomorphism(e, A; initial=(E=[1],)));

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

m = homomorphism(e, state(hset); initial=(V=1:2,E=[1]))
rewrite!(hset, A_rule, m)
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
omap = homomorphism(e, X; initial=(V=1:2,))
r = homomorphism(e, tri; initial=(V=1:2,))
hset = IncHomSet(ee, [r], X);
addition!(hset, r, omap)
@test validate(hset)


# Monic contraints
#----------------
mset = IncHomSet(G2, [create(Graph(1))], G2; monic=true);
@test mset isa IncCCHomSet
@test length(matches(mset)) == 2
M_rule = Rule(id(Graph()), create(Graph(1)); monic=true)
rewrite!(mset, M_rule)
@test length.(match_vect(mset)) == [2, 0, 4]

# Application conditions: NAC removing morphisms during addition!
#----------------------------------------------------------------
del = delete(Graph(1))
mset = IncHomSet(Graph(1), [del], G2⊕T; nac=[del]);
@test length(keys(mset)) == 2
M_rule = Rule(id(Graph(1)), delete(Graph(1)); ac=[NAC(del)])
m = ACSetTransformation(Graph(1), G2⊕T; V=[1])
rewrite!(mset, M_rule, m)
@test length(keys(mset)) == 1
rewrite!(mset, M_rule)
@test length(keys(mset)) == 0
@test isnothing(rewrite!(mset, M_rule))

# Application conditions: NAC adding morphisms during deletion!
#--------------------------------------------------------------
del = homomorphism(⊕(Graph[fill(T, 2); Graph(1)]), 
                   state(mset); initial=(V=1:3,)) # delete one loop
deletion!(mset, del)
@test length(keys(mset)) == 1
del = homomorphism(⊕(Graph[T; G2]), 
                   state(mset); initial=(V=1:3,)) # delete another loop
deletion!(mset, del)
@test length(keys(mset)) == 2

del = homomorphism(Graph(3), state(mset); initial=(V=1:3,)) # delete another loop
deletion!(mset, del)
@test length(keys(mset)) == 3

# NAC with DPO optimization
#--------------------------
edge_loop = @acset Graph begin V=2; E=2; src=[1,1]; tgt=[1,2] end
to_edge_loop = homomorphism(e, edge_loop; monic=true)
# rem edge, not if src has loop
r = Rule(homomorphism(G2, e; initial=(V=1:2,)), id(G2);
         ac=[NAC(to_edge_loop; monic=true)]);

mset = IncHomSet(r, edge_loop);
@test length(keys(mset)) == 1
rewrite!(mset, r)
@test length(keys(mset)) == 1
rewrite!(mset, r)
@test length(keys(mset)) == 0

# Application conditions: PAC removing morphisms during deletion!
#----------------------------------------------------------------
# Remove edge, only if src has loop (no monic constraint on PAC)
r = Rule(homomorphism(G2, e; initial=(V=1:2,)), id(G2);
         ac=[PAC(to_edge_loop)]);
mset = IncHomSet(r, edge_loop ⊕ e);
m1, m2 = get_matches(r, state(mset)) # first one removes the loop
rewrite!(mset, r, m1)
@test length(keys(mset)) == 0
mset = IncHomSet(r, edge_loop ⊕ e);
rewrite!(mset, r, m2)
@test length(keys(mset)) == 1
rewrite!(mset, r)
@test length(keys(mset)) == 0

# Application conditions: PAC adding morphisms during addition!
#----------------------------------------------------------------
edge_loop′ = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,2] end
to_edge_loop′ = homomorphism(e, edge_loop′; monic=true)
r = Rule(id(e), to_edge_loop′;
         ac=[PAC(to_edge_loop; monic=true), 
             NAC(to_edge_loop′; monic=true)]);
G = @acset Graph begin V=4; E=4; src=[1,1,2,3]; tgt=[1,2,3,4] end
mset = IncHomSet(r, G);
# there is just one 'way' in which apply R unlocks new matches from this PAC
@test length(only(values(mset.constraints.pac[1].overlaps))) == 1
@test length(keys(mset)) == 1
rewrite!(mset, r)
@test length(keys(mset)) == 1
@test ne(state(mset)) == 5
rewrite!(mset, r)
@test length(keys(mset)) == 1
@test ne(state(mset)) == 6
rewrite!(mset, r)
@test length(keys(mset)) == 0
@test ne(state(mset)) == 7

# Non-monic match causing problems
if false 
  A_rule = Rule(id(Graph(2)), 
                homomorphism(Graph(2), path_graph(Graph, 2); monic=true));
  start =ob(terminal(Graph));
  hset = IncHomSet(path_graph(Graph, 3), [A_rule.R], start);
  rewrite!(hset, A_rule);
  validate(hset)
end

# Weighted Graph
#---------------
if false # has same non-monic match problem as above
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

rewrite!(hset, A_rule)
@test validate(hset)
end

# DDS 
#-----
@present SchDDS(FreeSchema) begin X::Ob; Φ::Hom(X,X) end
@acset_type DDS(SchDDS, index=[:Φ])
DDS(i::Int) = @acset DDS begin X=i; Φ=[rand(1:i) for _ in 1:i] end
DDS(phi::Vector{Int}) = @acset DDS begin X=(length(phi)); Φ=phi end

I = DDS([1,2,1])
r = ACSetTransformation(I, DDS([1,2,1,1]); X=[1, 2, 3])
start = DDS([1])
m = homomorphism(I, start)
hset = IncHomSet(DDS([1,1,1]), [r], start);
rewrite!(hset, Rule(id(I), r), m)
@test validate(hset)

# Labeled Set
#-----------
@present SchLSet(FreeSchema) begin X::Ob; D::AttrType; f::Attr(X,D) end
@acset_type LSet(SchLSet){Symbol}
rep = @acset LSet begin X=1; D=1; f=[AttrVar(1)] end # representable X
rep2 = @acset LSet begin X=2;D=1;f=[AttrVar(1),AttrVar(1)] end
start = @acset LSet begin X=1; f=[:X] end

f = homomorphism(rep, rep2; any=true)
hset = IncHomSet(start, [f], start);
@test length(hset.static.overlaps[f])==1
@test length(keys(hset)) == 1;
rewrite!(hset, Rule(id(rep), f))
validate(hset)
rewrite!(hset, Rule(id(rep), f))
validate(hset)


# SPO-inspired example
#---------------------

@present SchFirm(FreeSchema) begin 
  (P,F,J,V)::Ob; 
  v::Hom(V,F); p::Hom(J,P); f::Hom(J,F)
end
@acset_type Firm(SchFirm)
P = @acset Firm begin P=1 end
F = @acset Firm begin P=1 end
J = @acset Firm begin J=1;F=1;P=1;f=1;p=1 end
V = @acset Firm begin V=1;F=1;v=1 end

nac = homomorphism(P⊕V, J⊕V)

init =@acset Firm begin F=2; J=1; P=2; V=1; f=[1]; p=[2]; v=[2] end
next = @acset Firm begin F=2; P=1; V=1; v=[2] end
upd = homomorphism(next, init; initial=(F=1:2,P=[1]))

# We look for Person+Vacancy pairs such that the person isn't already employed
mset = IncHomSet(P⊕V, ACSetTransformation[], init; nac=[nac]);
deletion!(mset, upd)
validate(mset)

end # module
