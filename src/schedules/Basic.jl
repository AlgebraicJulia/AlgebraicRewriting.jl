module Basic 
export Weaken, Strengthen, Initialize 

using Catlab.CategoricalAlgebra

using ...CategoricalAlgebra.CSets: Migrate
using ..Wiring: AgentBox, Traj, traj_agent, id_pmap, tot_pmap
import ..Wiring: input_ports, output_ports, initial_state, color, update

"""
Change the agent to a subset of the current agent without changing the world
"""
struct Weaken <: AgentBox
  name::String 
  agent::ACSetTransformation # map A₂ -> A₁
end  
Base.string(c::Weaken) = c.name
input_ports(r::Weaken) = [codom(r.agent)] 
output_ports(r::Weaken) = [dom(r.agent)]
initial_state(::Weaken) = nothing 
color(::Weaken) = "lavender"
(F::Migrate)(a::Weaken) =  Weaken(a.name,F(a.agent))
function update(r::Weaken, ::Int, instate::Traj, ::Nothing)
  last_step = traj_agent(instate) # A -> X 
  return (1, r.agent ⋅ last_step, id_pmap(codom(last_step)), nothing, "")
end 


"""
Add to both agent and the state of the world via a pushout.
"""
struct Strengthen <: AgentBox
  name::String 
  agent::ACSetTransformation # map A₁ -> A₂
end  
Base.string(c::Strengthen) = c.name
input_ports(r::Strengthen) = [dom(r.agent)] 
output_ports(r::Strengthen) = [codom(r.agent)]
initial_state(::Strengthen) = nothing 
color(::Strengthen) = "lightgreen"
(F::Migrate)(a::Strengthen) =  Strengthen(a.name,F(a.agent))
function update(r::Strengthen, ::Int, instate::Traj, ::Nothing)
  last_step = traj_agent(instate) # A -> X 
  world_update, new_agent = pushout(last_step, r.agent)
  return (1, new_agent, tot_pmap(world_update),  nothing, "")
end 


"""
A box that spits out a constant ACSet with an empty agent above it. Possibly, 
it does not take any inputs, so it can act as a comonoid counit.
"""
struct Initialize <: AgentBox
  name::String 
  state::StructACSet 
  in_agent::Union{Nothing,StructACSet}
  Initialize(s, in_agent=nothing, n="") = new(n,s,in_agent)
end
Base.string(c::Initialize) = c.name
input_ports(r::Initialize) = isnothing(r.in_agent) ? [] : [r.in_agent] 
output_ports(r::Initialize) = [typeof(r.state)()]
initial_state(::Initialize) = nothing 
color(::Initialize) = "gray"
(F::Migrate)(a::Initialize) = Initialize(a.name,F(a.state),F(a.in_agent))
function update(r::Initialize, ::Int, instate::Traj, ::Nothing)
  last_state = traj_re(instate) 
  return (1, create(r.state), no_pmap(last_state,r.state),  nothing, "")
end 

end # module 