module Basic 
export Weaken, Strengthen, Initialize, Fail

using StructEquality

using Catlab.CategoricalAlgebra, Catlab.Theories

using ...Rewrite
using ...Rewrite.Inplace: interp_program!
using ...CategoricalAlgebra.CSets: Migrate
using ..Poly
using ..Wiring: AgentBox
import ..Wiring: input_ports, output_ports, initial_state, color, update!
import ACSets: sparsify

# Weakening 
###########

"""
Change the agent to a subobject of the current agent without changing the world
"""
@struct_hash_equal struct Weaken <: AgentBox
  name::Symbol 
  agent::ACSetTransformation # map A₂ -> A₁
end  
Weaken(agent::ACSetTransformation) = Weaken(Symbol(""), agent)
input_ports(r::Weaken) = [codom(r.agent)] 
output_ports(r::Weaken) = [dom(r.agent)]
initial_state(::Weaken) = nothing 
color(::Weaken) = "lavender"
(F::Migrate)(a::Weaken) =  Weaken(a.name,F(a.agent))
sparsify(a::Weaken) = Weaken(a.name, sparsify(a.agent))

function update!(::Ref, boxdata::Weaken, g::ACSetTransformation, inport::Int; cat)
  inport == 1 || error("Weaken has exactly 1 input")
  compose[cat](boxdata.agent, g), 1, ""
end

# Strengthening
###############

"""
Adds to both agent and the state of the world via a pushout.

        Agent₁  →  Agent₂
          ↓          ⇣    
        World₁ -->⌜World₂ 
"""
@struct_hash_equal struct Strengthen <: AgentBox
  name::Symbol 
  agent::ACSetTransformation # map A₁ -> A₂
  prog::RewriteProgram
  function Strengthen(n::Symbol, agent::ACSetTransformation; cat=nothing)
    cat = isnothing(cat) ? infer_acset_cat(agent) : cat

    new(n, deepcopy(agent), compile_rewrite(Rule(id[cat](dom(agent)), agent)))
  end
end  
Strengthen(agent::ACSetTransformation) = Strengthen(Symbol(""), agent)

input_ports(r::Strengthen) = [dom(r.agent)] 
output_ports(r::Strengthen) = [codom(r.agent)]
initial_state(::Strengthen) = nothing 
color(::Strengthen) = "lightgreen"
(F::Migrate)(a::Strengthen) =  Strengthen(a.name,F(a.agent))
sparsify(a::Strengthen) = Strengthen(a.name, sparsify(a.agent))

function update!(::Ref, boxdata::Strengthen, g::ACSetTransformation, inport::Int; cat)
  inport == 1 || error("Strengthen has exactly 1 input")
  rmap = interp_program!(boxdata.prog, g.components, codom[cat](g))
  new_agent = ACSetTransformation(rmap, codom[cat](boxdata.agent), codom[cat](g); cat)
  new_agent, 1, ""
end

# Initialization
################

"""
A box that spits out a constant ACSet with an empty agent above it. Possibly, 
it does not take any inputs, so it can act as a comonoid counit.
"""
@struct_hash_equal struct Initialize <: AgentBox
  name::Symbol
  state::StructACSet 
  in_agent::Union{Nothing,StructACSet}
  Initialize(s, in_agent=nothing, n=Symbol("")) = 
    new(n, deepcopy.([s, in_agent])...)
end
input_ports(r::Initialize) = isnothing(r.in_agent) ? [] : [r.in_agent] 
output_ports(r::Initialize) = [typeof(r.state)()]
initial_state(::Initialize) = nothing 
color(::Initialize) = "gray"
(F::Migrate)(a::Initialize) = Initialize(a.name,F(a.state),F(a.in_agent))
sparsify(a::Initialize) = Initialize(a.name, sparsify([a.state,a.in_agent])...)

function update(i::Initialize, t::PMonad)
  update_i(::Nothing,w::WireVal;kw...) = MealyRes(nothing,[
    (t == Maybe ? nothing : 1, WireVal(1,disjoint(w.val, create(i.state))))], "")
end 

function update!(::Ref, boxdata::Initialize, ::ACSetTransformation, inport::Int)
  inport == 1 || error("Initialize has exactly 1 input")
  return create(i.state), 1, ""
end

# Failure
#########

@struct_hash_equal struct Fail <: AgentBox
  agent::ACSet
  silent::Bool
  name::String
  Fail(a::ACSet, silent=false, name="Fail") = new(deepcopy(a), silent, name)
end 

input_ports(r::Fail) = [r.agent] 

output_ports(::Fail) = []

initial_state(::Fail) = nothing 

color(::Fail) = "red"

(F::Migrate)(a::Fail) = Fail(F(a.agent), a.silent, a.name)

sparsify(a::Fail) = Fail(sparsify(a.agent), a.silent, a.name)

function update(f::Fail, ::PMonad=Maybe)
  update_f(::Nothing,w; kw...) = f.silent ? MealyRes(nothing,[],"fail") : error("$S $w")
end

update!(::Ref, boxdata::Fail, ::ACSetTransformation, inport::Int) = error("Fail")



end # module
