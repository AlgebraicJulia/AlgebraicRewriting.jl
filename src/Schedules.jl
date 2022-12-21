module Schedules
export Schedule, Traj, nports, mk_sched, traj_res, typecheck,
       Query, RuleApp, Weaken, Strengthen, Condition, 
       loop_rule, const_cond, if_cond, has_match,
       uniform, merge_wires, while_schedule, for_schedule, agent,
       rewrite_schedule, apply_schedule, migrate_schedule, graphviz
       

using DataStructures, Random

using Catlab, Catlab.CategoricalAlgebra, Catlab.WiringDiagrams, Catlab.Theories
using Catlab.Programs
using ..Rewrite
using ..Rewrite: rewrite_with_match, get_matches, postcompose_partial, instantiate
using ..CSets: extend_morphism_constraints, extend_morphisms, homomorphisms
using Catlab.CategoricalAlgebra.DataMigrations: MigrationFunctor
using Catlab.WiringDiagrams.DirectedWiringDiagrams: in_port_id, out_port_id
using .CSets

const homs = homomorphisms

import Base: map
import Catlab.WiringDiagrams: ocompose
import Catlab.Graphics: to_graphviz, LeftToRight
import Catlab.Theories: compose, otimes, ⋅, ⊗
import Catlab.WiringDiagrams.DirectedWiringDiagrams: input_ports,output_ports

"""
The true "primitive" is the Scientist category, which works for morphisms of any 
level of generality (e.g. composites). However, our effective primitives are: 
  RuleApp, Condition, Query, Weaken/Strengthen Agent, and Initialize.

There are also higher level patterns built from these generating morphisms.
"""

# String utilities 
##################
"""Visualize the data of a CSet homomorphism"""
str_hom(m::ACSetTransformation) = join([
  "$k: $(collect(c))" for (k,c) in pairs(components(m))
  if !isempty(collect(c.func))], '\n')

# Partial map utilities 
#######################
id_pmap(s::StructACSet) = Span(id(s),id(s)) # the identity partial map
no_pmap(s1::StructACSet,s2::StructACSet) = Span(create.([s1,s2])...) # empty
tot_pmap(f::ACSetTransformation) = Span(id(dom(f)), f)

# General wiring diagram utilities
###################################
"""Identity WD"""
nports(i::Int, agent::StructACSet) = id(Ports(fill(agent, i)))

"""Feed the last n outputs into the last n inputs of a WD""" 
function mk_trace(w::WiringDiagram, n::Int)
  ips, ops = input_ports(w), output_ports(w)
  wd = WiringDiagram(ips[1:end-n], ops[1:end-n])
  add_box!(wd, Box(ips, ops))
  add_wires!(wd, [
    [Wire(ip, (input_id(wd),i),(1,i)) for (i,ip) in enumerate(ips[1:end-n])]...,
    [Wire(op, (1,i),(output_id(wd),i)) for (i,op) in enumerate(ops[1:end-n])]...,
    [Wire(ip, (1,i+n),(1,i+n)) for (i,ip) in enumerate(ips[end-n+1 : end])]...])
  ocompose(wd, [w])
end 

"""Make a wiring diagram with ob/hom generators using @program macro"""
function mk_sched(args::NamedTuple, n_trace::Int, 
                  kw::Union{NamedTuple,AbstractDict}, wd::Expr)
  os = Dict(k=>v for (k,v) in collect(pairs(kw)) if v isa StructACSet)
  hs = Dict(k=>(v isa AgentBox ? singleton(v) : v) for (k,v) in collect(pairs(kw))
            if v isa Union{WiringDiagram,AgentBox})
  P = Presentation(FreeSymmetricMonoidalCategory)
  os_ = Dict(v=>add_generator!(P, Ob(FreeSymmetricMonoidalCategory, k)) 
             for (k,v) in collect(os))
  for (k,v) in collect(hs)
    add_generator!(P, Hom(k, otimes([os_[ip] for ip in input_ports(v)]),
                            otimes([os_[op] for op in output_ports(v)])))
  end
  args_ = Expr(:tuple,[Expr(Symbol("::"), k,v) for (k,v) in pairs(args)]...)
  wd = mk_trace(parse_wiring_diagram(P, args_, wd), n_trace)

  for x in Symbol.(["$(x)_port_type" for x in [:outer_in,:outer_out,:out,:in]])
    wd.diagram[:,x] = [kw[v] for v in wd.diagram[x]]
  end
  return ocompose(wd, [hs[b.value] for b in boxes(wd)])
end 


# General Trajectory and Schedule datatypes 
###########################################

struct TrajStep 
  desc::String
  world::ACSetTransformation
  pmap::Span{<:StructACSet}
  inwire::Wire
  outwire::Wire
end 

"""
Structure of a trajectory of a "world state" that is generated via traversal of 
a schedule. The data for each step in time is a world state (with a 
distinguished agent) as well as a wire ID that one is living on. Furthermore,
between the world states, there are partial maps to show how they are related 
to each other.
"""
mutable struct Traj
  initial::ACSetTransformation 
  steps::Vector{TrajStep}
  Traj(i::ACSetTransformation) = new(i, TrajStep[])
end 
Base.last(t::Traj) = last(t.steps)
Base.isempty(t::Traj) = isempty(t.steps)
Base.length(t::Traj) = length(t.steps)
Base.getindex(t::Traj, i::Int) = t.steps[i]
get_agent(t::Traj, i::Int) = i == 0 ? t.initial : t[i].world
traj_res(s::Traj) = codom(traj_agent(s))
traj_agent(t::Traj) = isempty(t.steps) ? t.initial : last(t).world
Base.push!(t::Traj, ts::TrajStep) = push!(t.steps, ts)

"""
Take a morphism (pointing at world state #i) and push forward to current time.
"""
function update_agent(t::Traj, i::Int, a::ACSetTransformation)
  if i < 0
    error("Called update with negative index $i")
  elseif i == length(t) # special case
    codom(a) == codom(get_agent(t, i)) || error("BAD MATCH $i $a")
    return a
  end 
  codom(a) == codom(left(t[i+1].pmap)) || error("BAD MATCH $i $a")
  for j in i+1:length(t)
    a = postcompose_partial(t[j].pmap, a)
  end
  codom(a) == traj_res(t) || error("Failed to postcompose")
  return a 
end

"""
Type for primitive boxes used in a schedule. These are the generating morphisms
of a traced monoidal category, with objects being lists of ACSets.
"""
abstract type AgentBox end 
mk_box(a::AgentBox) = Box(a, input_ports(a), output_ports(a))
Base.show(io::IO, c::AgentBox) = show(io, string(c))

input_ports(::AgentBox)::Vector{StructACSet} = error("Not yet defined")
output_ports(::AgentBox)::Vector{StructACSet} = error("Not yet defined")
initial_state(::AgentBox) = error("Not yet defined") 
color(::AgentBox) = error("Not yet defined") 
(::MigrationFunctor)(::AgentBox) = error("Not yet defined")

""" In x P x S -> Out x P x S x Msg ---- output P actually just needs the maps
Xₙ₋₁ -/-> X and A -> X, which get concatenated to the input trajectory P
"""
update(::AgentBox, inport::Int, instate::Traj) = error("Not yet defined") 

"""Make a wiring diagram around a box"""
function singleton(b::AgentBox)::Schedule
  ips, ops = input_ports(b), output_ports(b)
  wd = Schedule(ips, ops)
  add_box!(wd, mk_box(b))
  add_wires!(wd, [
    [Wire(ip,(input_id(wd),i),(1,i)) for (i, ip) in enumerate(ips)]...,
    [Wire(op,(1,i),(output_id(wd),i)) for (i, op) in enumerate(ops)]...,])
  return wd 
end
# Automatically call singleton when composing boxes w/ wiring diagrams
compose(x::AgentBox, y::Union{WiringDiagram, AgentBox}) = compose(singleton(x), y)
compose(x::WiringDiagram, y::AgentBox) = compose(x, singleton(y))
⋅(x::AgentBox, y::Union{WiringDiagram, AgentBox}) = ⋅(singleton(x), y)
⋅(x::WiringDiagram, y::AgentBox) = ⋅(x, singleton(y))
otimes(x::AgentBox, y::Union{WiringDiagram, AgentBox}) = otimes(singleton(x), y)
otimes(x::WiringDiagram, y::AgentBox) = otimes(x, singleton(y))
⊗(x::AgentBox, y::Union{WiringDiagram, AgentBox}) = ⊗(singleton(x), y)
⊗(x::WiringDiagram, y::AgentBox) = ⊗(x, singleton(y))


# It would be nice if ⊗ and ⋅ preserved the type of WDs, then we could more 
# strongly type our code.
const Schedule = WiringDiagram{Any, StructACSet, StructACSet, AgentBox}

"""Map a functor over the data of a schedule"""
function migrate_schedule(F::MigrationFunctor, wd::WiringDiagram) 
  wd = deepcopy(wd)
  for x in [:value, Symbol.(["$(x)_port_type" for x in 
                            [:outer_in,:outer_out,:out,:in]])..., 
                    Symbol.(["$(x)wire_value" for x in ["",:in_,:out_]])...]
    wd.diagram[:,x] = F.(wd.diagram[x])
  end 
  return wd
end 

function typecheck(wd::WiringDiagram)::Schedule 
  wd = deepcopy(wd)
  function checkfun(s::Symbol,t::Symbol, wval::Symbol, sval::Symbol, tval::Symbol)
    for (i, (op, ip)) in enumerate(zip(wd.diagram[s], wd.diagram[t]))
      d = Dict(:w=>wd.diagram[i,wval], :s=>wd.diagram[op, sval],
               :t=>wd.diagram[ip, tval])
      val = Set(filter(x->!isnothing(x), collect(values(d))))
      if length(val) != 1 error("#$i ($s:$op->$t:$ip): $(collect(d))") end 
      set_subpart!(wd.diagram, i,  wval, only(val))
      set_subpart!(wd.diagram, op, sval, only(val))
      set_subpart!(wd.diagram, ip, tval, only(val))
    end 
  end 
  checkfun(:src,:tgt,:wire_value,:out_port_type,:in_port_type)
  checkfun(:in_src,:in_tgt,:in_wire_value,:outer_in_port_type,:in_port_type)
  checkfun(:out_src,:out_tgt,:out_wire_value,:out_port_type,:outer_out_port_type)

  wd2 = Schedule([],[])
  copy_parts!(wd2.diagram, wd.diagram)
  return wd2
end 

graphviz(wd::WiringDiagram; kw...) = to_graphviz(wd; 
  node_colors=Dict(i=>color(b.value) for (i,b) in enumerate(boxes(wd))), kw...)

# Primitive AgentBoxes 
######################
"""
Has the semantics of applying the rule to *some* match that is found 
(no guarantees on which one, which should be controlled by application 
conditions).

The agent is related to the L and R patterns of the rule. 
"""
struct RuleApp <: AgentBox
  name::String 
  rule::Rule 
  agent::Span # map L <-- A --> R
  RuleApp(n,r::Rule, a::Multispan) = new(n,r,Span(a...))
  RuleApp(n,r::Rule, a::ACSetTransformation) = 
    RuleApp(n,r,Span(a⋅r.L, a⋅r.R))
  RuleApp(n,r::Rule, a::StructACSet; kw...) = 
    RuleApp(n,r,only(homs(a, dom(r.L); kw...)))
  RuleApp(n,r::Rule) = 
    RuleApp(n,r,create(dom(r.L))) # empty interface by default
end  
Base.string(c::RuleApp) = c.name
input_ports(r::RuleApp) = [dom(left(r.agent))] 
output_ports(r::RuleApp) = input_ports(r)
color(::RuleApp) = "lightblue"
initial_state(::RuleApp) = nothing 
(F::MigrationFunctor)(a::RuleApp) = RuleApp(a.name,F(a.rule), F(a.agent))

function update(r::RuleApp, ::Int, instate::Traj, ::Nothing)
  last_step = traj_agent(instate) # A -> X 
  init = extend_morphism_constraints(last_step, left(r.agent))
  ms = get_matches(r.rule, codom(last_step);initial=init)
  if isempty(ms)
    return (1, last_step, id_pmap(codom(last_step)), nothing, "(no match)")
  else 
    m = first(ms)
    r′ ,m′ = m isa LooseACSetTransformation ? instantiate(r.rule, m) : (r.rule, m)
    res = rewrite_match_maps(r′, m′)
    new_agent = right(r.agent) ⋅ get_rmap(ruletype(r.rule), res)
    pmap = get_pmap(ruletype(r.rule), res)
    msg = str_hom(m)
    return (1, new_agent, pmap, nothing, msg)
  end
end 

"""
A primitive box in a NestedDWD which does not change the state but redirects it 
out of one of n wires. 

It contains a function (A->X) -> ℝⁿ. This optionally depends on the internal 
state. This weights probability for n outports, conditional on the status of an 
ACSet.

The state and update function are by default trivial.
"""
struct Condition <: AgentBox
  name::String 
  prob::Function                  # ACSetTransformation (x S) -> ℝⁿ
  update::Union{Nothing,Function} # ACSetTransformation x S -> S
  n::Int
  agent::StructACSet
  init::Any
  Condition(r,n,a;name="",update=nothing,init=nothing) = 
    new(name,r,update,n,a,init)
end
Base.string(c::Condition) = c.name
input_ports(c::Condition) = [c.agent] 
output_ports(c::Condition) = fill(c.agent, c.n) 
initial_state(c::Condition) = c.init
color(::Condition) = "lightpink"

# WARNING: the update/prob functions hide their ACSet dependence in code, so 
# data migration cannot update these parts which may cause runtime errors.
(F::MigrationFunctor)(a::Condition) = 
  Condition(a.prob, a.n, F(a.agent); update=a.update, name=a.name, init=a.init)

"""Allow `prob` to depend on just the input or optionally the state, too"""
apply_prob(c::Condition, arg1, arg2) = try 
  return c.prob(arg1,arg2)
catch e 
  if e isa MethodError 
    return c.prob(arg1)
  else 
    throw(e)
  end
end

function update(c::Condition, ::Int, instate::Traj, boxstate::Any)
  curr_state = traj_res(instate)
  dist = apply_prob(c, curr_state, boxstate)
  outdoor = findfirst(q -> q > rand(), cumsum(dist) ./ sum(dist))
  newstate = isnothing(c.update) ? nothing : c.update(instate,boxstate)
  state_msg = "$boxstate ↦ $newstate"
  msg = "$dist" * (all(isnothing, [newstate, boxstate]) ? "" : "\n$state_msg") 
  return (outdoor, traj_agent(instate), id_pmap(curr_state), newstate, msg)
end

"""
Has an A input/output and a B input/output (by default, the B input can be 
changed to some other type if needed). Performs one action
per element of Hom(B,A) (i.e. sends you out along the B wire with agent Bₙ->X
). After you have done this for all Bₙ, then you exit the A port (you need to 
update the A->X map, and, if at any point the agent was deleted, then you exit a 
third door typed by 0).
Optional: give a partial map from A->B so that only B agents that are related 
to the current A agent are found.
"""
struct Query <: AgentBox
  name::String
  agent::Span
  return_type::StructACSet
  Query(a::Span, n::String="", ret=nothing) = 
    new(n,a, isnothing(ret) ? codom(right(a)) : ret)
  Query(a_out::StructACSet, n::String="", ret=nothing) =
    Query(typeof(a_out)(), a_out, n, ret)
  Query(a_in::StructACSet,a_out::StructACSet, n::String="", ret=nothing) = 
    Query(no_pmap(a_in,a_out), n, ret)
end

mutable struct QueryState 
  enter_time::Int 
  homs::Vector{ACSetTransformation}
end
Base.isempty(q::QueryState) = isempty(q.homs)
Base.pop!(q::QueryState) = pop!(q.homs)
Base.length(q::QueryState) = length(q.homs)
Base.string(c::Query) = "Query $(c.name)"
color(::Query) = "yellow"
in_agent(c::Query) = codom(left(c.agent))
out_agent(c::Query) = codom(right(c.agent))
input_ports(c::Query) = [in_agent(c), c.return_type] 
output_ports(c::Query) = [in_agent(c), out_agent(c), typeof(in_agent(c))()]
initial_state(::Query) = QueryState(-1, ACSetTransformation[])
(F::MigrationFunctor)(a::Query) =  Query(a.name,F(a.agent), F(a.return_type))

function update(q::Query, i::Int, instate::Traj, boxstate::Any)
  println("entering update with i $i and boxstate $boxstate")
  idp = id_pmap(traj_res(instate))
  msg = ""
  curr_boxstate = (i != 1) ? boxstate : begin 
    ms = extend_morphisms(left(q.agent)⋅traj_agent(instate), right(q.agent))
    msg *= "Found $(length(ms)) agents"
    QueryState(length(instate), ms)
  end 

  if isempty(curr_boxstate) # END
    new_agent = update_agent(instate, curr_boxstate.enter_time, 
                             get_agent(instate,curr_boxstate.enter_time))
    if isnothing(new_agent) # original agent gone
      msg *= "\nCannot recover original agent."
      curr_boxstate.enter_time = -1
      return (3, create(traj_res(instate)), idp, curr_boxstate,msg)
    else # original agent recovered
      msg *= "\nExiting with original agent."
      curr_boxstate.enter_time = -1
      return (1, new_agent, idp, curr_boxstate,msg)
    end 
  else # CONTINUE 
    println("LENGTH INSTATE $(length(instate)) curr_boxstate.enter_time $(curr_boxstate.enter_time)")
    new_agent = update_agent(instate, curr_boxstate.enter_time, pop!(curr_boxstate))
    
    msg *= "\nContinuing ($(length(curr_boxstate)) queued) with \n" * str_hom(new_agent)
    println("LEAVING W/ BOXSTATE $curr_boxstate")
    return (2, new_agent,idp,curr_boxstate,msg)
  end 
end


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
(F::MigrationFunctor)(a::Weaken) =  Weaken(a.name,F(a.agent))
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
(F::MigrationFunctor)(a::Strengthen) =  Strengthen(a.name,F(a.agent))
function update(r::Strengthen, ::Int, instate::Traj, ::Nothing)
  last_step = traj_agent(instate) # A -> X 
  world_update, new_agent = pushout(last_step, r.agent)
  return (1, new_agent, tot_pmap(world_update),  nothing, "")
end 


"""
Add to both agent and the state of the world via a pushout.
"""
struct Initialize <: AgentBox
  name::String 
  state::StructACSet 
  in_agent::StructACSet 
  Initialize(s, n="", i=nothing) = new(n,s,isnothing(i) ? typeof(s)() : i)
end  
Base.string(c::Initialize) = c.name
input_ports(r::Initialize) = [r.in_agent] 
output_ports(r::Initialize) = [typeof(r.state)()]
initial_state(::Initialize) = nothing 
color(::Initialize) = "gray"
(F::MigrationFunctor)(a::Initialize) = Initialize(a.name,F(a.state),F(a.in_agent))
function update(r::Initialize, ::Int, instate::Traj, ::Nothing)
  last_state = traj_re(instate) 
  return (1, create(r.state), no_pmap(last_state,r.state),  nothing, "")
end 

# Helpful ways of constructing schedules 
########################################

"""Create a branching point with fixed probabilities for each branch"""
const_cond(v::Vector{Float64}, agent::StructACSet, ;name=nothing) = 
  Condition(_->v,length(v),agent; name=isnothing(name) ? "const $v" : name)

"""A uniform chance of leaving each of n branches"""
uniform(n::Int, agent::StructACSet) = const_cond(fill(1/n,n), agent; name="uniform")

"""Enter the 1st branch iff the world state evaluates to true""" 
if_cond(name::String, boolfun::Function, agent::StructACSet) = 
  Condition((x,_)->boolfun(x) ? [1,0] : [0,1], 2, agent; name=name)

"""
A box that takes the first output iff there is a match from a rule into the 
current state"""
has_match(rulename::String, r::Rule, agent::StructACSet) = 
  if_cond("Can match $rulename", x->!isempty(get_matches(r,x)), agent)

"""
The comonoid structure - merging multiple wires into one. This is unproblematic
because the world state only ever exists on one wire at a given time.
"""
function merge_wires(n::Int, agent::StructACSet)::Schedule
  wd = Schedule(fill(agent,n),[agent])
  add_wires!(wd, [Wire(agent,(input_id(wd),i),(output_id(wd),1)) for i in 1:n])
  return wd
end

"""Perform a 1-1 schedule until a condition is met"""
function while_schedule(s::WiringDiagram, boolfun::Function; name::String="while")
  err = "While pattern requires a schedule with inputs [A] and outputs [A]"
  ip, op = ipop = input_ports(s),output_ports(s)
  a, a′ = only.(ipop)
  a == a′ || error(err)
  wd = WiringDiagram(input_ports(s),output_ports(s))
  add_boxes!(wd, [Box(ip,op), Box(ip,vcat(op,op))])
  add_wires!(wd, [Wire(a,(input_id(wd),1),(1,1)), Wire(a,(1,1),(2,1)),
                  Wire(a,(2,1),(1,1)), Wire(a,(2,2),(output_id(wd),1))])
  return ocompose(wd, [s, singleton(if_cond(name, boolfun, a))])
end
while_schedule(s::AgentBox, boolfun::Function; name::String="while") = 
  while_schedule(singleton(s), boolfun; name=name)

loop_rule(a::RuleApp) =
  while_schedule(a, x->!isempty(get_matches(a.rule,x)); name="match $(a.name)")
 

"""Perform a 1-1 schedule `n` times"""
function for_schedule(s_::WiringDiagram, n::Int)
  s = typecheck(s_)
  a = only(input_ports(s))
  a == only(output_ports(s)) || error("for_schedule ports not 1-1")
  forblock = Condition((_,i) -> i>0 ? [0., 1] : [1., 0], 2, a; name="for 1:$n",
                       update=(_,i) -> i - 1, init=n)
  return mk_sched((init=:A, trace_arg=:A,), 1, Dict(
    :forb => forblock, :sched=>s,  :A=>a), quote 
      out, loop = forb([init, trace_arg])
      return out, sched(loop)
  end)
end

for_schedule(s::AgentBox, n::Int) = for_schedule(singleton(s),n)

function agent(s::WiringDiagram, a::Union{Span,StructACSet}; n="agent", ret=nothing)
  q = Query(a, n, ret)
  a,b,z = output_ports(q)
  a_, c = input_ports(q)
  a == a_ || error("Bad ports")

  mk_sched((init=:A, trace_arg=:C,), 1, (
    query = q, sched=s, A=a, B=b, C=c, Z=z), quote 
      out, loop, _ = query(init, trace_arg)
      return out, sched(loop)
  end)
end 



# Executing schedules 
#####################

"""
Execute a single primitive box (either a Condition or a NamedRule).
Return output wire.
"""
function apply_schedule_step(s::Schedule, P::Traj, S::AbstractVector, 
                             iw::Wire)::Wire 
  I = iw.target # in port
  box = boxes(s)[I.box]
  O, dP₁, dP₂, S′, msg = update(box.value, I.port, P, S[I.box])
  S[I.box] = S′ # update the box state 
  ow = only(out_wires(s, Port(I.box,OutputPort,O))) # no branching allowed!
  println("$(box.value.name)\n$msg")
  push!(P, TrajStep("$(box.value.name)\n$msg", dP₁, dP₂, iw, ow))
  return ow
end

"""Execute an entire schedule. Optionally limit # of steps"""
function apply_schedule(s_::WiringDiagram,g::ACSetTransformation; in_port=1,
                        steps::Int=-1)::Traj
  s = typecheck(s_)
  input_ports(s)[in_port] == dom(g) || error("Bad input agent to schedule")
  P = Traj(g)
  boxstates = [initial_state(b) for b in s.diagram[:value]]
  curr_wire = only(out_wires(s, Port(input_id(s),OutputPort,in_port)))
  while (steps != 0) && (curr_wire.target.box != output_id(s))
    steps -= 1
    curr_wire = apply_schedule_step(s, P, boxstates, curr_wire)
  end 
  return P
end

# assuming input has 0 agent.
apply_schedule(s::WiringDiagram,g::StructACSet; kw...) = 
  apply_schedule(s, create(g); kw...)

"""Just get the result from applying the schedule"""
rewrite_schedule(s::WiringDiagram, G; kw...) = 
  traj_res(apply_schedule(s, G; kw...))


end # module
