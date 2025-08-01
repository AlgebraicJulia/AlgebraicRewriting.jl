module Conditionals 
export Conditional, const_cond, if_cond, uniform, while_schedule, for_schedule

using StructEquality

using Catlab.CategoricalAlgebra, Catlab.WiringDiagrams

using ...CategoricalAlgebra.CSets: Migrate
using ..Wiring, ..Poly
using ..Wiring: AgentBox
import ACSets: sparsify
import ..Wiring: input_ports, output_ports, initial_state, color, update!

"""
A primitive box in a NestedDWD which does not change the state but redirects it 
out of one of n wires. 

It contains a function (A->X) -> ℝⁿ. This optionally depends on the internal 
state. This weights probability for n outports, conditional on the status of an 
ACSet. If the function just depends on X rather than the whole morphism, 
`withagent` is `false`. If the function does not depend on the internal state 
(assumed to be true iff initial state is `nothing`), then `withstate` is `false`.

The state and update function are by default trivial.
"""
@struct_hash_equal struct Conditional <: AgentBox
  name::Symbol 
  prob::Function                  # ACSetTransformation (x S) -> ℝⁿ
  update::Union{Nothing,Function} # ACSetTransformation x S -> S
  n::Int
  agent::StructACSet
  init::Any
  withagent::Bool
  withstate::Bool
  function Conditional(r, n, a; name="", update=nothing, init=nothing, 
                       withagent=false, withstate=nothing) 
    withstate = isnothing(withstate) ? !isnothing(init) : withstate # default
    new(name, r, update, n, deepcopy(a), init, withagent, withstate)
  end
end

input_ports(c::Conditional) = [c.agent]

output_ports(c::Conditional) = fill(c.agent, c.n)

initial_state(c::Conditional) = c.init

color(::Conditional) = "lightpink"

# WARNING: the update/prob functions hide their ACSet dependence in code, so 
# data migration cannot update these parts which may cause runtime errors.
(F::Migrate)(a::Conditional) = 
  Conditional(a.prob, a.n, F(a.agent); update=a.update, name=a.name, init=a.init)

sparsify(a::Conditional) = 
  Conditional(a.prob, a.n, sparsify(a.agent); update=a.update, name=a.name, init=a.init)

function update!(state::Ref, boxdata::Conditional, g::ACSetTransformation, inport::Int; cat)
  inport == 1 || error("Conditionals have exactly 1 input")
  in_arg = boxdata.withagent ? g : codom(g)
  dist = boxdata.withstate ? boxdata.prob(in_arg, state[]) : boxdata.prob(in_arg)
  outdoor = findfirst(q -> q > rand(), cumsum(dist) ./ sum(dist))
  newstate = isnothing(boxdata.update) ? nothing : boxdata.update(g, state[])
  state_msg = isnothing(state[]) && isnothing(newstate) ? "" : "$(state[]) ↦ $newstate"
  msg = string(dist) * " " * state_msg
  state[] = newstate
  (g, outdoor, msg)
end

"""Create a branching point with fixed probabilities for each branch"""
const_cond(v::Vector{Float64}, agent::StructACSet; name=nothing) = 
  Conditional(_->v, length(v), agent; name=isnothing(name) ? Symbol("const $v") : name)

"""A uniform chance of leaving each of n branches"""
uniform(n::Int, agent::StructACSet) = const_cond(fill(1/n,n), agent; name=:uniform)

"""Enter the 1st branch iff the world state evaluates to true""" 
if_cond(name::Symbol, boolfun::Function, agent::StructACSet; withagent=false) = 
  Conditional(x->boolfun(x) ? [1,0] : [0,1], 2, agent; name, withagent)

"""Perform a 1-1 schedule until a condition is met"""
function while_schedule(s::Schedule, boolfun::Function; name=:while, withagent=false)
  err = "While pattern requires a schedule with inputs [A] and outputs [A]"
  a, a′ = only.([input_ports(s.d),output_ports(s.d)])
  a == a′ || error(err)
  ic = singleton(if_cond(name, boolfun, a; withagent))
  mk_sched((trace_arg=:X,),(init=:X,),Names(X=a),(iff=ic,f=s), quote 
    if_t, if_f = iff([init,trace_arg])
    return f(if_t), if_f
  end)
end

while_schedule(s::AgentBox, boolfun::Function; name=:while, withagent=false) = 
  while_schedule(singleton(s), boolfun; name, withagent)


"""Perform a 1-1 schedule `n` times"""
function for_schedule(s_::Schedule, n::Int)
  s = typecheck(s_)
  a = only(input_ports(s.d))
  a == only(output_ports(s.d)) || error("for_schedule ports not 1-1")
  name = Symbol("for 1:$n")
  forblock = Conditional((_,i) -> i>0 ? [0., 1] : [1., 0], 2, a; name,
                       update=(_,i) -> i - 1, init=n)
  mk_sched((trace_arg=:A,),(init=:A,), Names(Dict(:A=>a,)), Dict(
    :forb => forblock, :sched=>s), quote 
      out, loop = forb([init, trace_arg])
      return sched(loop), out
  end)
end

for_schedule(s::AgentBox, n::Int) = for_schedule(singleton(s), n)

end # module
