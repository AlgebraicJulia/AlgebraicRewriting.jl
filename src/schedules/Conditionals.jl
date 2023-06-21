module Conditionals 
export Conditional, const_cond, if_cond, uniform, while_schedule, for_schedule

using Catlab.CategoricalAlgebra, Catlab.WiringDiagrams

using ...CategoricalAlgebra.CSets: Migrate
using ..Wiring, ..Poly
using ..Wiring: AgentBox
import ..Wiring: input_ports, output_ports, initial_state, color, update
using ..Eval: Traj, id_pmap, traj_res, nochange, traj_agent

"""
A primitive box in a NestedDWD which does not change the state but redirects it 
out of one of n wires. 

It contains a function (A->X) -> ℝⁿ. This optionally depends on the internal 
state. This weights probability for n outports, conditional on the status of an 
ACSet.

The state and update function are by default trivial.
"""
struct Conditional <: AgentBox
  name::Symbol 
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

function update(c::Conditional, p::PMonad=Maybe)#, ::Int, instate::Traj, ::Nothing)
  p ∈ [Maybe, List, Dist] || error("Unexpected monad $p")
  function update_conditional(S, w::WireVal; kw...)
    w.wire_id == 1 || error("Conditionals have exactly 1 input")
    if c.argtype == :world 
      curr_state = traj_res(w.val)
    elseif c.argtype == :agent 
      curr_state = traj_agent(w.val)
    else 
      curr_state = w.val
    end 
    dist = apply_prob(c, curr_state, S)
    outdoor = findfirst(q -> q > rand(), cumsum(dist) ./ sum(dist))
    newstate = isnothing(c.update) ? nothing : c.update(curr_state, S)
    state_msg = "$S ↦ $newstate"
    msg = "$dist" * (all(isnothing, [newstate, S]) ? "" : "\n$state_msg") 
    wv = WireVal(outdoor, nochange(w.val))
    return MealyRes(newstate,[(p == Maybe ? nothing : 1, wv)], msg)
  end
end



"""Create a branching point with fixed probabilities for each branch"""
const_cond(v::Vector{Float64}, agent::StructACSet, ;name=nothing) = 
  Conditional(_->v,length(v),agent; name=isnothing(name) ? Symbol("const $v") : name)

"""A uniform chance of leaving each of n branches"""
uniform(n::Int, agent::StructACSet) = const_cond(fill(1/n,n), agent; name=:uniform)

"""Enter the 1st branch iff the world state evaluates to true""" 
if_cond(name::Symbol, boolfun::Function, agent::StructACSet; argtype=:world) = 
  Conditional((x,_)->boolfun(x) ? [1,0] : [0,1], 2, agent; name=name, argtype=argtype)


"""Perform a 1-1 schedule until a condition is met"""
function while_schedule(s::Schedule, boolfun::Function; name=:while, argtype=:world)
  err = "While pattern requires a schedule with inputs [A] and outputs [A]"
  a, a′ = only.([input_ports(s.d),output_ports(s.d)])
  a == a′ || error(err)
  ic = singleton(if_cond(name, boolfun, a; argtype=argtype))
  return mk_sched((trace_arg=:X,),(init=:X,),Names(X=a),(iff=ic,f=s), quote 
    if_t, if_f = iff([init,trace_arg])
    return f(if_t), if_f
  end)
end
while_schedule(s::AgentBox, boolfun::Function; name=:while, argtype=:world) = 
  while_schedule(singleton(s), boolfun; name=name, argtype=argtype)


"""Perform a 1-1 schedule `n` times"""
function for_schedule(s_::Schedule, n::Int)
  s = typecheck(s_)
  a = only(input_ports(s.d))
  a == only(output_ports(s.d)) || error("for_schedule ports not 1-1")
  forblock = Conditional((_,i) -> i>0 ? [0., 1] : [1., 0], 2, a; name=Symbol("for 1:$n"),
                       update=(_,i) -> i - 1, init=n)
  return mk_sched((trace_arg=:A,),(init=:A,), Names(Dict(:A=>a,)), Dict(
    :forb => forblock, :sched=>s), quote 
      out, loop = forb([init, trace_arg])
      return sched(loop), out
  end)
end

for_schedule(s::AgentBox, n::Int) = for_schedule(singleton(s),n)

end # module
