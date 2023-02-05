module Wiring
export Schedule,Traj, TrajStep, mk_sched, typecheck, merge_wires, 
       singleton, id_wires, id_wire, traj_res, traj_agent

using Catlab.CategoricalAlgebra, Catlab.WiringDiagrams, Catlab.Programs, Catlab.Theories
import Catlab.WiringDiagrams.DirectedWiringDiagrams: input_ports,output_ports
import Catlab.Theories: compose, otimes, ⋅, ⊗
using ...CategoricalAlgebra.CSets
using ...CategoricalAlgebra.CSets: abstract

"""
The true "primitive" is the Scientist category, which works for morphisms of any 
level of generality (e.g. composites). However, our effective primitives are: 
  RuleApp, Conditional, Query, Weaken/Strengthen Agent, and Initialize.

There are also higher level patterns built from these generating morphisms.
"""

# String utilities 
##################
"""Visualize the data of a CSet homomorphism"""
str_hom(m::ACSetTransformation) = join([
  "$k: $(collect(c))" for (k,c) in pairs(components(m))
  if !isempty(collect(c))], '\n')

# Partial map utilities 
#######################

id_pmap(s::StructACSet) = Span(abstract(s),abstract(s)) # the identity partial map
no_pmap(s1::StructACSet,s2::StructACSet) = Span(create.([s1,s2])...) # empty
tot_pmap(f::ACSetTransformation) = Span(id(dom(f)), f)

noattr(s::StructACSet{S}) where S = all(a->nparts(s,a) == 0, attrtypes(S))
noattr(s::ACSetTransformation) = noattr(codom(s))

# General wiring diagram utilities
###################################
"""Identity WD"""
id_wires(i::Int, agent::StructACSet) = id(Ports(fill(agent, i)))
id_wire(agent::StructACSet) = id_wires(1, agent)

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

"""
Make a wiring diagram with ob/hom generators using @program macro

TODO double check that this does not introduce any wire splitting.
"""
function mk_sched(args::NamedTuple, n_trace::Int, 
                  kw::Union{NamedTuple,AbstractDict}, wd::Expr)
  os = Dict(k=>v for (k,v) in collect(pairs(kw)) if v isa StructACSet)
  hs = Dict(k=>(v isa AgentBox ? singleton(v) : v) for (k,v) in collect(pairs(kw))
            if v isa Union{WiringDiagram,AgentBox})
  P = Presentation(FreeSymmetricMonoidalCategory)
  os_ = Dict(v=>add_generator!(P, Ob(FreeSymmetricMonoidalCategory, k)) 
             for (k,v) in collect(os))
  for (k,v) in collect(hs)
    i = (isempty(input_ports(v)) 
        ? munit(FreeSymmetricMonoidalCategory.Ob) 
        : otimes([os_[ip] for ip in input_ports(v)]))
    add_generator!(P, Hom(k, i, otimes([os_[op] for op in output_ports(v)])))
  end
  args_ = Expr(:tuple,[Expr(Symbol("::"), k,v) for (k,v) in pairs(args)]...)
  wd = mk_trace(parse_wiring_diagram(P, args_, wd), n_trace)

  for x in Symbol.(["$(x)_port_type" for x in [:outer_in,:outer_out,:out,:in]])
    wd.diagram[:,x] = [kw[v] for v in wd.diagram[x]]
  end
  return ocompose(wd, WiringDiagram[hs[b.value] for b in boxes(wd)])
end 


# General Trajectory and Schedule datatypes 
###########################################

struct TrajStep 
  desc::String
  world::ACSetTransformation
  pmap::Span{<:StructACSet} # nothing == id
  inwire::Wire
  outwire::Wire
  function TrajStep(d,w,p,i,o)
    noattr(w) || error("World state has variables $w")
    codom(right(p)) == codom(w) || error("World doesn't match pmap")
    return new(d,w,p,i,o)
  end
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
function update_agent(t::Traj, i::Int, a::ACSetTransformation; check=false)
  !check || is_natural(a) || error("Updating unnatural a")
  noattr(a) || error("World state has variables")
  if i < 0
    error("Called update with negative index $i")
  elseif i == length(t) # special case
    codom(a) == codom(get_agent(t, i)) || error("BAD MATCH $i $a")
    return a
  end 
  codom(a) == codom(left(t[i+1].pmap)) || error("BAD MATCH $i $a")
  for j in i+1:length(t)
    a = postcompose_partial(t[j].pmap, a)
    if check && !is_natural(a) 
      println("dom(a)"); show(stdout, "text/plain", dom(a))
      println("codom(a)"); show(stdout, "text/plain", codom(a))
      error("Updated unnatural a $(collect(pairs(components(a))))")
    end
    if isnothing(a) return nothing end 
  end
  codom(a) == traj_res(t) || error("Failed to postcompose $(codom(a))\n$(traj_res(t))")
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
(::Migrate)(::AgentBox) = error("Not yet defined")

""" In x P x S -> Out x P x S x Msg ---- output P actually just needs the maps
Xₙ₋₁ -/-> X and A -> X, which get concatenated to the input trajectory P
"""
update(::AgentBox, iid_wire::Int, instate::Traj) = error("Not yet defined") 

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
function (F::Migrate)(wd::WiringDiagram) 
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
      inbox, outbox = wd.diagram[op, :out_port_box], wd.diagram[ip, :in_port_box]
      if length(val) != 1 error("#$i ($s($inbox) ->$t($outbox): $(collect(d))") end 
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



"""
The comonoid structure - merging multiple wires into one. This is unproblematic
because the world state only ever exists on one wire at a given time.
"""
function merge_wires(n::Int, agent::StructACSet)::Schedule
  wd = Schedule(fill(agent,n),[agent])
  add_wires!(wd, [Wire(agent,(input_id(wd),i),(output_id(wd),1)) for i in 1:n])
  return wd
end

end # module 