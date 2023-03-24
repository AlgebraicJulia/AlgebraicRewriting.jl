module Eval 
export Traj, TrajStep, apply_schedule, rewrite_schedule, traj_res

using Catlab.CategoricalAlgebra, Catlab.WiringDiagrams

using ..Wiring, ..Poly
using ..Wiring: initial_state, AgentBox, update
using ...CategoricalAlgebra.CSets
using ...CategoricalAlgebra.CSets: abstract
import ..Poly: Mealy, apply_schedule

"""
This is a simple way of handling evaluation of diagrams which only works 
in the Maybe monad setting.
"""

# Partial map utilities 
#######################

id_pmap(s::StructACSet) = Span(abstract(s),abstract(s)) # the identity partial map
no_pmap(s1::StructACSet,s2::StructACSet) = Span(create.([s1,s2])...) # empty
tot_pmap(f::ACSetTransformation) = Span(id(dom(f)), f)

noattr(s::StructACSet{S}) where S = all(a->nparts(s,a) == 0, attrtypes(S))
noattr(s::ACSetTransformation) = noattr(codom(s))


# General Trajectory and Schedule datatypes 
###########################################


"""    A
       ↓
Xₙ₋₁ ↛ Xₙ
"""
struct TrajStep 
  world::ACSetTransformation
  pmap::Span{<:ACSet}
  function TrajStep(w,p)
    noattr(w) || error("World state has variables $w")
    codom(right(p)) == codom(w) || error("World doesn't match pmap")
    return new(w,p)
  end
end 

"""
A₁   A₂   ... Aₙ
↓    ↓        ↓
X₁ ↛ X₂ ↛ ... Xₙ
"""
struct Traj
  initial::ACSetTransformation 
  steps::Vector{TrajStep}
end
Traj(i::ACSetTransformation) = Traj(i, TrajStep[])
Traj(i::ACSet) = Traj(create(i), TrajStep[])

Base.last(t::Traj) = last(t.steps)
Base.isempty(t::Traj) = isempty(t.steps)
Base.length(t::Traj) = length(t.steps)
Base.getindex(t::Traj, i::Int) = t.steps[i]
get_agent(t::Traj, i::Int) = i == 0 ? t.initial : t[i].world
traj_res(s::Traj) = codom(traj_agent(s))
traj_agent(t::Traj) = isempty(t.steps) ? t.initial : last(t).world
nochange(t::Traj) = add_step(t,
  TrajStep(traj_agent(t), id_pmap(traj_res(t))))
add_step(t::Traj,ts::TrajStep) = Traj(t.initial, vcat(t.steps,[ts]))

disjoint(t::Traj, new_agent::ACSetTransformation) = add_step(t, 
  TrajStep(new_agent, no_pmap(traj_res(t),codom(new_agent))))

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


# Executing schedules 
#####################

Mealy(a::AgentBox, p::PMonad) = Mealy(update(a,p),p,initial_state(a))

function apply_schedule(s::Schedule,g::Any,t::PMonad=Maybe; kwargs...)
  # Replace Agents with Mealy
  w = WiringDiagram([],[])
  copy_parts!(w.diagram, s.d.diagram)
  w.diagram[:box_type] = Box{Mealy}
  w.diagram[:value] = Mealy.(w.diagram[:value], Ref(t))

  apply_schedule(w, Traj(g), t; kwargs...)
end

"""Just get the result from applying the schedule"""
rewrite_schedule(s::Schedule, G; kw...) = 
  traj_res(apply_schedule(s, G; kw...))



end # module 
