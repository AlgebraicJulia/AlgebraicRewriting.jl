module TestInplace

using Test, Catlab, AlgebraicRewriting
using AlgebraicRewriting.Rewrite.Inplace: compile_rewrite

# Toggle a light switch
#######################

# Datatypes
@present SchLightSwitch(FreeSchema) begin
  X::Ob
  State::AttrType
  switch::Attr(X,State)
end

@acset_type AbsLightSwitch(SchLightSwitch, part_type=BitSetParts)


const Switch = AbsLightSwitch{Bool}

𝒞S = ACSetCategory(MADVarACSetCat(Switch()))

mk_switch(b::Union{Nothing,Bool}=nothing) = @acset Switch begin 
  X=1; State=Int(isnothing(b)); switch=[isnothing(b) ? AttrVar(1) : b] 
end

# Specific switches 
T, F = mk_switch.(Bool[1,0])

Pat = mk_switch()

# toggle rule 
flip(xs) = !only(xs)

create[𝒞S](Pat)

toggle = Rule(create[𝒞S](Pat), create[𝒞S](Pat); expr=(State=[flip],), cat=𝒞S)

# Apply rewrite
prog = compile_rewrite(toggle)

# @test F == rewrite(toggle, T; cat=𝒞S) # WE CAN'T DO THIS YET 

m= homomorphism(Pat, T; cat=𝒞S)
rewrite_match!(toggle, m; prog, cat=𝒞S);
@test is_isomorphic(T, F; cat=𝒞S)


# Sum parallel edges of Weighted Graph 
######################################
# Datatypes
@acset_type MADWeightedGraph(SchWeightedGraph, part_type=BitSetParts, 
                             index=[:src,:tgt]) <: AbstractGraph
const MADIntGraph = MADWeightedGraph{Int}
const Grph = ACSetCategory(MADVarACSetCat(MADIntGraph))

# Specific graphs
L = @acset MADIntGraph begin 
  V=2; E=2; Weight=2; src=1; tgt=2; weight=AttrVar.(1:2) 
end

R = @acset MADIntGraph begin 
  V=2; E=1; Weight=1; src=1; tgt=2; weight=[AttrVar(1)] 
end

G = @acset MADIntGraph begin V=1; E=3; src=1; tgt=1; weight=[10,20,100] end
# to_graphviz(G; edge_labels=:weight)

# Rule
l, r = homomorphism.(Ref(MADIntGraph(2)), [L, R]; initial=(V=1:2,), cat=Grph)

plus(xs) = xs[1] + xs[2]

rule = Rule(l, r; monic=[:E], expr=Dict(:Weight=>[plus]), cat=Grph)

# Apply rewrite
prog = compile_rewrite(rule)

m = get_matches(rule, G,cat=Grph)[1]
f = rewrite_match!(rule, m; cat=Grph)

@test get(f.components[:Weight])(1) == Right(30)

end # module
