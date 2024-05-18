module TestIncremental 

using Test
using AlgebraicRewriting
using Catlab
using AlgebraicRewriting.Incremental: 
  validate, connected_acset_components, state, deletion!, addition!, runtime,
  IncSumHomSet, IncCCHomSet, match_vect
using AlgebraicRewriting.Rewrite.Utils: get_result, get_rmap, get_pmap
using Random

Random.seed!(100)

# test connected_acset_components
#--------------------------------
g1, g2 = path_graph.(Graph, [3, 2]);
ccs, iso = connected_acset_components(g1 ⊕ g2);
@test is_monic(iso) && is_epic(iso)
@test collect(first(ccs.cocone)[:V]) == [1,2,3] 

# Graph incremental hom search
#-----------------------------
                                                                  #  • ⇉ •
e, ee = path_graph.(Graph, 2:3)                                   #   ↘ ↙
A = @acset Graph begin V=3; E=4; src=[1,1,1,2]; tgt=[2,2,3,3] end #    •
A_rule = Rule(id(e), homomorphism(e, A));

# Empty edge case
hset = IncHomSet(Graph(), [A_rule.R], Graph(3)); 
@test length(matches(hset)) == 1
@test only(keys(hset)) == (1=>1)
@test hset[1] == hset[1=>1]

# Single connected component pattern
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

# Multiple connected components in pattern
hset = IncHomSet(ee ⊕ e, [A_rule.R], start);

@test haskey(hset, [1=>2, 1=>2])
@test !haskey(hset, [2=>2, 1=>2])
@test length(keys(hset)) == 9
@test hset[[1=>3,1=>3]] == hset[9]
del, add = rewrite!(hset, A_rule, homomorphisms(e, start)[2]);

@test isempty(del)

@test length.(match_vect(runtime(hset).components[1])) == [3,0,6]
@test length.(match_vect(runtime(hset).components[2])) == [3,0,3]
@test length(add) == 6*(3+3) + (3+6)*3
@test validate(hset)

@test Set(matches(hset)) == Set(homomorphisms(ee ⊕ e, state(hset)))
rewrite!(hset, A_rule);
@test validate(hset)
@test Set(matches(hset)) == Set(homomorphisms(ee ⊕ e, state(hset)))

@test hset == IncSumHomSet(hset)
roundtrip = IncSumHomSet(IncCCHomSet(hset));
@test roundtrip isa IncSumHomSet

# Blog example
tri = @acset Graph begin V=3;E=3;src=[1,1,2];tgt=[3,2,3]end
X = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,2] end
omap = homomorphism(e, X)
hset = IncHomSet(ee, [homomorphism(e, tri)], X);
addition!(hset, 1, omap)
@test validate(hset)

# Multiple connected components 
hset = IncHomSet(Graph(1) ⊕ e, [A_rule.R], start);
rewrite!(hset, A_rule, homomorphisms(e, start)[2]);
@test validate(hset)
rewrite!(hset, A_rule)
@test validate(hset)
@test length(keys(hset)) == 45

# Monic contraints
mset = IncHomSet(Graph(2), [create(Graph(1))], Graph(2); monic=true);
@test mset isa IncCCHomSet
@test length(matches(mset)) == 2
M_rule = Rule(id(Graph()), create(Graph(1)); monic=true)
rewrite!(mset, M_rule)
@test length.(match_vect(mset)) == [2, 4]

# Application conditions: NAC removing morphisms during addition!
del = delete(Graph(1))
mset = IncHomSet(Graph(1), [del], Graph(2)⊕ob(terminal(Graph)); nac=[del]);
@test length(keys(mset)) == 2
M_rule = Rule(id(Graph(1)), delete(Graph(1)); ac=[AppCond(del, false)])
rewrite!(mset, M_rule)
@test length(keys(mset)) == 1
rewrite!(mset, M_rule)
@test length(keys(mset)) == 0
@test isnothing(rewrite!(mset, M_rule))

# Application conditions: NAC adding morphisms during deletion!

match_vect(mset)
del = homomorphism(⊕(Graph[fill(ob(terminal(Graph)), 2); Graph(1)]), 
                   state(mset); monic=true) # delete one loop
deletion!(mset, del)
# Weighted Graph
const WG′ = WeightedGraph{Bool}
e, ee = path_graph.(WG′, 2:3)
e[:weight] = [AttrVar(add_part!(e, :Weight))]
ee[:weight] = [true, AttrVar(add_part!(ee, :Weight))]
A = @acset WG′ begin V=3; E=4; Weight=1; 
  src=[1,1,1,2]; tgt=[2,2,3,3]; weight=[AttrVar(1), true, false, true] 
end
A_rule = Rule(id(e), homomorphism(e, A); monic=true)

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

# Benchmark 
###########

all_graph(rng) = [cycle_graph.(Graph,rng); star_graph.(Graph, rng);
                  path_graph.(Graph, rng)]
rand_graph(rng) = rand(all_graph(rng))

while true
  L, R = rand_graph(3:5), rand_graph(3:5)
  I = rand(path_graph.(Graph, 2:4))
  NV=200
  start = erdos_renyi(Graph, NV, 2*NV)
  l = homomorphism(I, L; monic=true)
  r = homomorphism(I, R; monic=true)
  isnothing(r) && continue
  m = homomorphism(I, start)
  isnothing(m) && continue
  res = rewrite_match_maps(Rule(id(I), r), m);
  (pl, pr), rmap = get_pmap(:DPO, res), get_rmap(:DPO, res);
  @test collect(pl[:V]) == 1:NV

  @time begin 
    new_matches = homomorphisms(L, codom(rmap))
  end;
  hset = IncHomSet(L, [r], start);
  @time begin 
    deletion!(hset, pl);
    addition!(hset, 1, rmap, pr);
  end 
  validate(hset)
  break
end

# DDS 
#----
@present SchDDS(FreeSchema) begin X::Ob; Φ::Hom(X,X) end
@acset_type DDS(SchDDS, index=[:Φ])
DDS(i::Int) = @acset DDS begin X=i; Φ=[rand(1:i) for _ in 1:i] end

while true
  L, R, I, A, B = DDS.([5, 5, 5, 3, 3])
  l1,l2,r1,r2 = hs = [homomorphism(x...; monic=true) for x in 
                      [(A,L),(A,I),(B,I),(B,R)]]
  all(!isnothing, hs) || continue
  (_, l), (r, _) = pushout(l1,l2), pushout(r1,r2)
  rand_rule = Rule(l, r)

  start, pattern = DDS(2000), DDS(5)
  m = homomorphism(codom(l), start)
  (!isnothing(m) && isnothing(can_match(rand_rule, m))) || continue 

  res = rewrite_match_maps(rand_rule, m)
  (pl, pr), rmap = get_pmap(:DPO, res), get_rmap(:DPO, res)

  @time begin 
    new_matches = homomorphisms(pattern, codom(rmap))
  end;

  hset = IncHomSet(pattern, [rand_rule.R], start);
  GC.gc()
  @time begin 
    try 
    deletion!(hset, pl)
    addition!(hset, 1, rmap, pr)
  
    catch e 
      error("dom(r) $(dom(r))\ncodom(r) $(codom(r))\nr $r\npattern $pattern\nm$m")
    end
  end;
  break 
end

end # module 