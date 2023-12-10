module TestIncremental 

using Test
using AlgebraicRewriting
using Catlab
using AlgebraicRewriting.Incremental: validate, connected_acset_components, 
                                      state, deletion!, addition!
using AlgebraicRewriting.Rewrite.Utils: get_result, get_rmap, get_pmap
using Random

# test valid constraint
#----------------------
g1, g2 = path_graph.(Graph, [3,2])

add_edges!(g1, [1,2,3,2], [1,2,3,3])  # loops on each node and one double arrow
add_edge!(g2, 1, 2)  # double arrow
@test length(homomorphisms(g2, g1; valid=(V=Dict([1 => [1,3]]),))) == 3
@test length(homomorphisms(g2, g1; valid=(E=Dict([1 => [1,3]]),))) == 2

# test connected_acset_components
#--------------------------------
ccs, iso = connected_acset_components(g1⊕g2);
@test is_monic(iso) && is_epic(iso)
@test collect(first(ccs.cocone)[:V]) == [1,2,3] 

# Graph incremental hom search
#-----------------------------
                                                                  #  • ⇉ •
e, ee = path_graph.(Graph, 2:3)                                   #   ↘ ↙
A = @acset Graph begin V=3; E=4; src=[1,1,1,2]; tgt=[2,2,3,3] end #    •
A_rule = Rule(id(e), homomorphism(e, A); monic=true)

# Empty edge case
hset = IncHomSet(Graph(), [A_rule.R], Graph(3)); 
@test length(hset.matches) == 1

# Single connected component pattern
start = @acset Graph begin V=3; E=3; src=[1,2,3]; tgt=[2,3,3] end
hset = IncHomSet(ee, [A_rule.R], start);
rewrite!(hset, A_rule, homomorphisms(e, start)[2])
@test validate(hset)
rewrite!(hset, A_rule)
@test validate(hset)

# Multiple connected components in pattern
hset = IncHomSet(ee ⊕ e, [A_rule.R], start);
rewrite!(hset, A_rule, homomorphisms(e, start)[2])
@test validate(hset)
@test Set(matches(hset)) == Set(homomorphisms(ee ⊕ e, state(hset)))
rewrite!(hset, A_rule)
@test validate(hset)
@test Set(matches(hset)) == Set(homomorphisms(ee ⊕ e, state(hset)))

## DDS 
#-----
@present SchDDS(FreeSchema) begin X::Ob; Φ::Hom(X,X) end
@acset_type DDS(SchDDS, index=[:Φ])
DDS(i::Int) = @acset DDS begin X=i; Φ=[rand(1:i) for _ in 1:i] end
DDS(phi::Vector{Int}) = @acset DDS begin X=(length(phi)); Φ=phi end

p2 = DDS([2,2])
p22 = p2 ⊕ p2
R = DDS([2,2,4,4,4])
r = homomorphism(p22, R; monic=true)
hset = IncHomSet(p22, [r], p22);
rewrite!(hset, Rule(id(p22), r), id(p22))
@test validate(hset)


I = DDS([1,2,1])
R = DDS([1,2,1,1])
r = ACSetTransformation(I, R; X=[1, 2, 3])
pattern = DDS([1,1,1])
start = DDS([1])
m = homomorphism(I, start)
hset = IncHomSet(pattern, [r], start);
rewrite!(hset, Rule(id(I), r), m)
@test validate(hset)

# Benchmark 
###########

# for xxx in 1:100
#   println("XXX $xxx")
# erdos_renyi(Graph, 3, 3)
start =  @acset Graph begin V=3; E=3; src=[1,1,2]; tgt=[2,3,3] end
m = homomorphisms(e, start; monic=true)[2] # problem if  this is [2], not [1]

res = rewrite_match_maps(A_rule, m);
(pl, pr), rmap = get_pmap(:DPO, res), get_rmap(:DPO, res);

pattern = path_graph(Graph, 4) # path_graph(Graph,3)

# @time begin 
#   new_matches = homomorphisms(pattern, codom(rmap))
# end;
hset = IncHomSet(pattern, [A_rule.R], start);
@time begin 
  deletion!(hset, pl)
  addition!(hset, 1, rmap, pr)
end;

# 225 vs 318

o = hset.overlaps[1];
apex(o[225])
left(o[225])
right(o[225])
apex(o[318])
left(o[318])
right(o[318])

# end

@test Set(new_matches) == hset.matches

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
  println("HERE")
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