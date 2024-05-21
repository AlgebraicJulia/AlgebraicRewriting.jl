module TestIncrementalSum 

using Test
using AlgebraicRewriting, Catlab
using AlgebraicRewriting.Incremental.IncrementalCC: IncCCHomSet, match_vect
using AlgebraicRewriting.Incremental.IncrementalSum: IncSumHomSet
using AlgebraicRewriting.Incremental.IncrementalHom: runtime, state

                                                                  #  • ⇉ •
e, ee = path_graph.(Graph, 2:3)                                   #   ↘ ↙
A = @acset Graph begin V=3; E=4; src=[1,1,1,2]; tgt=[2,2,3,3] end #    •
A_rule = Rule(id(e), homomorphism(e, A));
start = @acset Graph begin V=3; E=3; src=[1,2,3]; tgt=[2,3,3] end

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
hset = IncHomSet(Graph(1) ⊕ e, [A_rule.R], start);
rewrite!(hset, A_rule, homomorphisms(e, start)[2]);
@test validate(hset)
rewrite!(hset, A_rule)
@test validate(hset)
@test length(keys(hset)) == 45

# DDS
#####
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

end # module
