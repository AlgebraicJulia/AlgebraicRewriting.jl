module Schedules
export NestedDWD, inner, outer, NPorts, 
       NamedRule, Condition, RuleSchedule, const_cond, if_cond, has_match,
       no_match, apply_schedule, uniform, merge_wires,
       ScheduleResult, rewrite_schedule, traj_res, WhileSchedule
      # rename_schedule

using DataStructures, Random

using Catlab, Catlab.CategoricalAlgebra, Catlab.WiringDiagrams, Catlab.Theories
using ..Rewrite
using ..Rewrite: rewrite_with_match, get_matches
using Catlab.CategoricalAlgebra.DataMigrations: MigrationFunctor

import Base: map
import Catlab.WiringDiagrams: ocompose
import Catlab.Graphics: to_graphviz, LeftToRight
import Catlab.Theories: dom, codom, id, compose, ⋅, ∘, otimes, ⊗, munit, braid, σ
import Catlab.WiringDiagrams.DirectedWiringDiagrams: input_ports,output_ports

# Schedule data structure
#########################
"""
These nested DWDs have as primitive boxes either 
"""
struct NestedDWD 
  outer::WiringDiagram
  inner::Vector{NestedDWD}
  NestedDWD(o::WiringDiagram, i = NestedDWD[]) = new(o, i)
end 
outer(d::NestedDWD) = d.outer 
inner(d::NestedDWD) = d.inner
input_ports(d::NestedDWD) = d |> outer |> input_ports
output_ports(d::NestedDWD) = d |> outer |> output_ports

function NestedDWD(b::Box) 
  wd = WiringDiagram(b.input_ports, b.output_ports)
  add_box!(wd,b)
  add_wires!(wd, Pair[[(input_id(wd),i)=>(1,i) for i in 1:length(b.input_ports)]...,
                  [(1,i)=>(output_id(wd),i) for i in 1:length(b.output_ports)]...])
  NestedDWD(wd)
end
struct NPorts 
  p::Ports 
  NPorts(n::Int) = new(Ports(fill(:X, n)))
  NPorts(p::Ports) = new(p)
end 

"""
This category instance allows NestedDWDs to be composed in series (⋅) and in 
parallel (⊗).
"""
@instance ThSymmetricMonoidalCategory{NPorts, NestedDWD} begin
  @import dom, codom

  id(A::NPorts) = NestedDWD(id(A.p))

  function compose(f::NestedDWD, g::NestedDWD)
    NestedDWD(f.outer⋅g.outer,vcat(f.inner, g.inner))
  end

  otimes(A::NPorts, B::NPorts) = NPorts(A.p ⊗ B.p)
  munit(::Type{NPorts}) = NPorts(0)

  otimes(f::NestedDWD, g::NestedDWD) = NestedDWD(f.outer⊗g.outer,vcat(f.inner, g.inner))

  braid(A::NPorts, B::NPorts) = NPorts(braid(A.p,B.p))
end

"""
Flatten a nested DWD into one that has no inner DWDs.
"""
function ocompose(d::NestedDWD)
  if isempty(d.inner) return d end 
  NestedDWD(ocompose(d.outer, [ocompose(i).outer for i in d.inner]))
end 

"""View a nested DWD as a flattened one"""
to_graphviz(d::NestedDWD; orientation=LeftToRight, kw...) = 
  to_graphviz(ocompose(d).outer; orientation=orientation, kw...)

"""
A primitive box in a NestedDWD which has the semantics of applying the rule to 
*some* match that is found (no guarantees on which one, which should be 
controlled by application conditions).
"""
struct NamedRule
  name::String 
  rule::Rule 
end 
Base.string(c::NamedRule) = c.name

"""
A primitive box in a NestedDWD which contains a function ACSet -> ℝⁿ.
This weights probability for n outports, conditional on the status of an ACSet.
"""
struct Condition 
  name::String 
  fun::Function
  n::Int
end

Base.string(c::Condition) = c.name

# Helpful ways of constructing schedules 
########################################

"""Create a branching point with fixed probabilities for each branch"""
const_cond(v::Vector{Float64};name=nothing) = 
  Box(Condition(isnothing(name) ? "const $v" : name, _->v,length(v)), 
      [:X],fill(:X,length(v)))

"""A uniform chance of leaving each of n branches"""
uniform(n::Int) = const_cond(fill(1/n,n); name="uniform")

"""Enter the 1st branch iff the world state evaluates to true""" 
if_cond(name::String, boolfun::Function) = 
  Box(Condition(name, x->boolfun(x) ? [1,0] : [0,1], 2),[:X],[:X,:X])

"""
A box that takes the first output iff there is a match from a rule into the 
current state"""
has_match(rulename::String, r::Rule) = 
  if_cond("Can match $rulename", x->!isempty(get_matches(r,x)))

"""
The comonoid structure - merging multiple wires into one. This is unproblematic
because the world state only ever exists on one wire at a given time.
"""
function merge_wires(n::Int)
  wd = WiringDiagram(fill(:X,n),[:X])
  add_wires!(wd, Pair[(input_id(wd),i)=>(output_id(wd),1) for i in 1:n])
  return NestedDWD(wd)
end

"""
Convert a rewrite rule into a small schedule, potentially looping until it 
can no longer match
"""
function RuleSchedule(n::String, r::Rule; loop::Bool=false)
  wd = WiringDiagram([:X],[:X])
  add_box!(wd,Box(NamedRule(n,r), [:X],[:X]))
  add_wires!(wd, Pair[(input_id(wd),1)=>(1,1),(1,1)=>(output_id(wd),1)])
  if loop
    rem_wire!(wd,only(in_wires(wd, output_id(wd))))
    add_box!(wd, has_match(n,r))
    add_wires!(wd, Pair[(1,1)=>(2,1), (2,1)=>(1,1), (2,2)=>(output_id(wd),1)])
  end
  NestedDWD(wd)
end

function WhileSchedule(s::NestedDWD, cond::Function; name::String="while")
  err = "Can only wrap a 1-in/1-out schedule with a while condition"
  length.([input_ports(s),output_ports(s)]) == [1,1] || error(err)
  wd = WiringDiagram([:X],[:X])
  add_boxes!(wd, [Box([:X],[:X]), Box([:X],[:X,:X])])
  add_wires!(wd, Pair[(input_id(wd),1)=>(1,1), (1,1)=>(2,1),(2,1)=>(1,1),
                      (2,2)=>(output_id(wd),1)])
  NestedDWD(wd, [s, NestedDWD(if_cond(name, cond))])
end

# Executing schedules 
#####################

"""The result of executing a schedule: a sequence of TrajSteps"""
struct TrajStep
  title::String # rule that got applied
  port::Pair{Int,Int}
  G::StructACSet # current graph
  m::Union{Nothing,ACSetTransformation} # match morphism that was used
  pmap::Union{Nothing,Span} # partial map into this graph
  TrajStep(t,p,g,m=nothing,pmap=nothing) = new(t,p,g,m,pmap)
end

function TrajStep(G::StructACSet)
  h=id(typeof(G)());
  TrajStep(:create, G, h, Span(h, create(G)))
end

const ScheduleResult = Vector{TrajStep}
traj_res(s::ScheduleResult) = last(s).G

"""
Execute a single primitive box (either a Condition or a NamedRule)
"""
function apply_schedule_step(s::WiringDiagram, g::StructACSet, box::Int)
  btype = s.diagram[box, :value]
  if btype isa Condition 
    dist = btype.fun(g)
    return findfirst(q -> q > rand(), cumsum(dist) ./ sum(dist))
  elseif btype isa NamedRule 
    return rewrite_with_match(btype.rule, g)
  else 
    error("Unknown semantics for $btype")
  end
end

"""
Execute an entire schedule.
"""
apply_schedule(s::NestedDWD,g::StructACSet; kw...) = 
  apply_schedule(ocompose(s).outer, g; kw...)

function apply_schedule(s::WiringDiagram,g::StructACSet; b::Int=0,p::Int=0, 
                        steps::Int=-1)::ScheduleResult
  b,p = (b,p) == (0,0) ? (input_id(s), 1) : (b, p)
  res = [TrajStep("start", b=>p, g, nothing, Span(id(g),id(g)))]
    
  while steps!=0 
    steps -= 1
    box = only(out_wires(s, Port(b,OutputPort,p))).target.box
    if box == output_id(s) return res end 
    boxval = s.diagram[box, :value]

    stepres = apply_schedule_step(s, g, box)
    if isnothing(stepres) # we failed to match a rule box 
      (b,p) = (box, 1) # nothing worth recording in the trajectory
    elseif stepres isa Int # we applied the condition and got an outport
      (b,p) = (box, stepres)
      push!(res, TrajStep(boxval.name, b=>p, g, nothing, Span(id(g), id(g))))
    else # we have a rewrite result 
      (b,p) = (box, 1)
      match, maps = stepres
      g, pmap = [f(ruletype(boxval.rule), maps) for f in [get_result, get_pmap]]
      push!(res,TrajStep(boxval.name, b=>p, g, match, pmap))
    end
  end 
  return res
end

"""Just get the result from applying the schedule"""
rewrite_schedule(s::WiringDiagram, G; kw...) = traj_res(apply_schedule(s, G; kw...))


"""Map a functor over the Rules in a schedule"""
(F::MigrationFunctor)(s::NestedDWD) = 
  NestedDWD(migrate(F, s.outer), [migrate(F,i) for i in s.inner])
migrate(F::MigrationFunctor, wd::WiringDiagram) = error("TODO")


# # Renaming schedules
# function sub_symb(sym::Symbol, d::Dict{String, String})
#   s = string(sym)
#   for (k,v) in collect(d)
#     s = replace(s, k=>v)
#   end
#   return Symbol(s)
# end
# rename_schedule(s::RuleSchedule{T}, n::Symbol) where T =
#   RuleSchedule(s.rule, n, s.match_prob)
# rename_schedule(s::ListSchedule, n::Symbol) = ListSchedule(s.rules, n)
# rename_schedule(s::WhileSchedule, n::Symbol) = WhileSchedule(s.sch, n, s.cond)
# rename_schedule(s::RuleSchedule{T}, n::Dict{String,String}) where T =
#   RuleSchedule(s.rule, sub_symb(s.name, n), s.match_prob)
# rename_schedule(s::ListSchedule, n::Dict{String,String}) =
#   ListSchedule(Schedule[rename_schedule(r,n) for r in s.rules], sub_symb(s.name, n))
# rename_schedule(s::WhileSchedule, n::Dict{String,String}) =
#   WhileSchedule(rename_schedule(s.sch,n), sub_symb(s.name, n), s.cond)

end # module
