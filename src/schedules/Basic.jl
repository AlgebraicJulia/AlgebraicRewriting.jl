module Basic 
export Weaken, Strengthen, Initialize, Fail

using Catlab.CategoricalAlgebra

using ...CategoricalAlgebra.CSets: Migrate
using ..Poly
using ..Wiring: AgentBox
import ..Wiring: input_ports, output_ports, initial_state, color, update
using ..Eval: Traj, TrajStep, traj_agent, id_pmap, tot_pmap, traj_res, add_step

"""
Change the agent to a subset of the current agent without changing the world
"""
struct Weaken <: AgentBox
  name::Symbol 
  agent::ACSetTransformation # map A₂ -> A₁
end  
Weaken(agent::ACSetTransformation) = Weaken(Symbol(""), agent)
input_ports(r::Weaken) = [codom(r.agent)] 
output_ports(r::Weaken) = [dom(r.agent)]
initial_state(::Weaken) = nothing 
color(::Weaken) = "lavender"
(F::Migrate)(a::Weaken) =  Weaken(a.name,F(a.agent))
function update(r::Weaken, p::PMonad=Maybe)
  function update_weaken(::Nothing,w; kw...) 
    ts = TrajStep(r.agent ⋅ traj_agent(w.val), id_pmap(traj_res(w.val)))
    wv = WireVal(1, add_step(w.val,ts))
   return  MealyRes(nothing,[(p==Maybe ? nothing : 1, wv)],"")
  end
end


"""
Adds to both agent and the state of the world via a pushout.
"""
struct Strengthen <: AgentBox
  name::Symbol 
  agent::ACSetTransformation # map A₁ -> A₂
end  
Strengthen(agent::ACSetTransformation) = Strengthen(Symbol(""), agent)

input_ports(r::Strengthen) = [dom(r.agent)] 
output_ports(r::Strengthen) = [codom(r.agent)]
initial_state(::Strengthen) = nothing 
color(::Strengthen) = "lightgreen"
(F::Migrate)(a::Strengthen) =  Strengthen(a.name,F(a.agent))
function update(r::Strengthen, t::PMonad)
  function update_strengthen(::Nothing,w::WireVal; kw...) 
    last_step = traj_agent(w.val) # A -> X 
    world_update, new_agent = pushout(last_step, r.agent)
    wv = WireVal(1, add_step(w.val, TrajStep(new_agent, tot_pmap(world_update))))
    return MealyRes(nothing,[(t == Maybe ? nothing : 1, wv)], "")
  end
end 


"""
A box that spits out a constant ACSet with an empty agent above it. Possibly, 
it does not take any inputs, so it can act as a comonoid counit.
"""
struct Initialize <: AgentBox
  name::Symbol
  state::StructACSet 
  in_agent::Union{Nothing,StructACSet}
  Initialize(s, in_agent=nothing, n="") = new(n,s,in_agent)
end
input_ports(r::Initialize) = isnothing(r.in_agent) ? [] : [r.in_agent] 
output_ports(r::Initialize) = [typeof(r.state)()]
initial_state(::Initialize) = nothing 
color(::Initialize) = "gray"
(F::Migrate)(a::Initialize) = Initialize(a.name,F(a.state),F(a.in_agent))
function update(i::Initialize, t::PMonad)
  update_i(::Nothing,w::WireVal;kw...) = MealyRes(nothing,[
    (t == Maybe ? nothing : 1, WireVal(1,disjoint(w.val, create(i.state))))], "")
end 


struct Fail <: AgentBox
  agent::ACSet
  silent::Bool
  name::String
  Fail(a::ACSet, silent=false, name="Fail") = new(a,silent,name)
end 
input_ports(r::Fail) = [r.agent] 
output_ports(::Fail) = []
initial_state(::Fail) = nothing 
color(::Fail) = "red"
(F::Migrate)(a::Fail) = Fail(F(a.agent))

function update(f::Fail, ::PMonad=Maybe)
  update_f(::Nothing,w; kw...) = f.silent ? MealyRes(nothing,[],"fail") : error("$S $w")
end

end # module 