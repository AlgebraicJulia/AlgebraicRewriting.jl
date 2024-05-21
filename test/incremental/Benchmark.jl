# informal benchmark
module Benchmark

using Test
using AlgebraicRewriting, Catlab
using Random
using AlgebraicRewriting.Rewrite.Utils:  get_rmap, get_pmap
using AlgebraicRewriting.Incremental.IncrementalHom: deletion!, addition!

Random.seed!(100)

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
    addition!(hset, r, rmap, pr);
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
    addition!(hset, rand_rule.R, rmap, pr)
  
    catch e 
      error("dom(r) $(dom(r))\ncodom(r) $(codom(r))\nr $r\npattern $pattern\nm$m")
    end
  end;
  break 
end

end # module
