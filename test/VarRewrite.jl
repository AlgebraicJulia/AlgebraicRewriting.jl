module VarRewrite
using Test
using AlgebraicRewriting
using Catlab.CategoricalAlgebra, Catlab.Graphs
using Catlab.ColumnImplementations: AttrVar

L = @acset WeightedGraph{Int} begin V=2; E=2; Weight=2; src=1; tgt=2; 
                                    weight=AttrVar.(1:2) end
I = WeightedGraph{Int}(2)
R = @acset WeightedGraph{Int} begin V=2; E=1; Weight=1; src=1; tgt=2; 
                                    weight=[AttrVar(1)] end

l = homomorphism(I,L; monic=true)
r = homomorphism(I,R; monic=true)
rule = Rule(l, r; monic=[:E], expr=Dict(:Weight=>[:(AttrVar(1)+AttrVar(2))]))

G = @acset WeightedGraph{Int} begin V=1; E=2; Weight=2; src=1; tgt=1; 
                                    weight=[10,20] end


@test rewrite(rule, G) == @acset WeightedGraph{Int} begin 
  V=1; E=1; src=1; tgt=1; weight=[30] end

end 