module Conditionals 
export Conditional, const_cond, if_cond, uniform, while_schedule, for_schedule

using Catlab.CategoricalAlgebra, Catlab.WiringDiagrams

using ...CategoricalAlgebra.CSets: Migrate
using ..Wiring
using ..Wiring: AgentBox, traj_agent, id_pmap
import ..Wiring: input_ports, output_ports, initial_state, color, update

"""
A primitive box in a NestedDWD which does not change the state but redirects it 
out of one of n wires. 

It contains a function (A->X) -> ℝⁿ. This optionally depends on the internal 
state. This weights probability for n outports, conditional on the status of an 
ACSet.

The state and update function are by default trivial.
"""
struct Conditional <: AgentBox
  name::String 
  prob::Function                  # ACSetTransformation (x S) -> ℝⁿ
  update::Union{Nothing,Function} # ACSetTransformation x S -> S
  n::Int
  agent::StructACSet
  init::Any
  argtype::Symbol
  Conditional(r,n,a;name="",update=nothing,init=nothing,argtype=:world) = 
    argtype ∈ [:world, :agent, :traj] ? new(name,r,update,n,a,init,argtype) : error(
      "Argtype $argtype must be world, agent, or traj")
end
Base.string(c::Conditional) = c.name
input_ports(c::Conditional) = [c.agent] 
output_ports(c::Conditional) = fill(c.agent, c.n) 
initial_state(c::Conditional) = c.init
color(::Conditional) = "lightpink"

# WARNING: the update/prob functions hide their ACSet dependence in code, so 
# data migration cannot update these parts which may cause runtime errors.
(F::Migrate)(a::Conditional) = 
  Conditional(a.prob, a.n, F(a.agent); update=a.update, name=a.name, init=a.init)

"""Allow `prob` to depend on just the input or optionally the state, too"""
apply_prob(c::Conditional, curr_state, box_state) = try 
  return c.prob(curr_state,box_state)
catch e 
  if e isa MethodError 
    return c.prob(curr_state)
  else 
    throw(e)
  end
end

function update(c::Conditional, ::Int, instate::Traj, boxstate::Any)
  curr_world = traj_res(instate)
  if c.argtype == :world 
    curr_state = curr_world
  elseif c.argtype == :agent 
    curr_state = traj_agent(instate)
  else 
    curr_state = instate
  end 
  dist = apply_prob(c, curr_state, boxstate)
  outdoor = findfirst(q -> q > rand(), cumsum(dist) ./ sum(dist))
  newstate = isnothing(c.update) ? nothing : c.update(instate,boxstate)
  state_msg = "$boxstate ↦ $newstate"
  msg = "$dist" * (all(isnothing, [newstate, boxstate]) ? "" : "\n$state_msg") 
  return (outdoor, traj_agent(instate), id_pmap(curr_world), newstate, msg)
end


"""Create a branching point with fixed probabilities for each branch"""
const_cond(v::Vector{Float64}, agent::StructACSet, ;name=nothing) = 
  Conditional(_->v,length(v),agent; name=isnothing(name) ? "const $v" : name)

"""A uniform chance of leaving each of n branches"""
uniform(n::Int, agent::StructACSet) = const_cond(fill(1/n,n), agent; name="uniform")

"""Enter the 1st branch iff the world state evaluates to true""" 
if_cond(name::String, boolfun::Function, agent::StructACSet; argtype=:world) = 
  Conditional((x,_)->boolfun(x) ? [1,0] : [0,1], 2, agent; name=name, argtype=argtype)


"""Perform a 1-1 schedule until a condition is met"""
function while_schedule(s::WiringDiagram, boolfun::Function; name::String="while", argtype=:world)
  err = "While pattern requires a schedule with inputs [A] and outputs [A]"
  ip, op = ipop = input_ports(s),output_ports(s)
  a, a′ = only.(ipop)
  a == a′ || error(err)
  wd = WiringDiagram(input_ports(s),output_ports(s))
  add_boxes!(wd, [Box(ip,op), Box(ip,vcat(op,op))])
  add_wires!(wd, [Wire(a,(input_id(wd),1),(1,1)), Wire(a,(1,1),(2,1)),
                  Wire(a,(2,1),(1,1)), Wire(a,(2,2),(output_id(wd),1))])
  return ocompose(wd, [s, singleton(if_cond(name, boolfun, a; argtype=argtype))])
end
while_schedule(s::AgentBox, boolfun::Function; name::String="while", argtype=:world) = 
  while_schedule(singleton(s), boolfun; name=name, argtype=argtype)


"""Perform a 1-1 schedule `n` times"""
function for_schedule(s_::WiringDiagram, n::Int)
  s = typecheck(s_)
  a = only(input_ports(s))
  a == only(output_ports(s)) || error("for_schedule ports not 1-1")
  forblock = Conditional((_,i) -> i>0 ? [0., 1] : [1., 0], 2, a; name="for 1:$n",
                       update=(_,i) -> i - 1, init=n)
  return mk_sched((init=:A, trace_arg=:A,), 1, Dict(
    :forb => forblock, :sched=>s,  :A=>a), quote 
      out, loop = forb([init, trace_arg])
      return out, sched(loop)
  end)
end

for_schedule(s::AgentBox, n::Int) = for_schedule(singleton(s),n)

end # module
