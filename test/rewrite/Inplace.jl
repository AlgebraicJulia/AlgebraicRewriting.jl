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

mk_switch(b::Union{Nothing,Bool}=nothing) = @acset Switch begin 
  X=1; State=Int(isnothing(b)); switch=[isnothing(b) ? AttrVar(1) : b] 
end

# Specific switches 
T, F = mk_switch.(Bool[1,0])

Pat = mk_switch()

# toggle rule 
flip(xs) = !only(xs)

toggle = Rule(id(Pat), id(Pat); expr=(State=[flip],))

# Apply rewrite
prog = compile_rewrite(toggle)

@test F == rewrite(toggle, T)

m= homomorphism(Pat, T)
is_natural(m)
can_match(toggle, m)

get_match(toggle, T)

rewrite_match!(toggle, m; prog);
@test T == F


# Sum parallel edges of Weighted Graph 
######################################
# Datatypes
@acset_type MADWeightedGraph(SchWeightedGraph, part_type=BitSetParts, 
                             index=[:src,:tgt]) <: AbstractGraph
const MADIntGraph = MADWeightedGraph{Int}

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
l, r = homomorphism.(Ref(MADIntGraph(2)), [L, R]; monic=true)

plus(xs) = xs[1] + xs[2]

rule = Rule(l, r; monic=[:E], expr=Dict(:Weight=>[plus]))

# Apply rewrite
prog = compile_rewrite(rule)

f = rewrite!(rule, G)

@test f.components[:Weight](AttrVar(1)) == 30

end # module
