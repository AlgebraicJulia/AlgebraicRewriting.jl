module Eval 
export Traj, TrajStep, apply_schedule, rewrite_schedule, traj_res

using Catlab, Catlab.CategoricalAlgebra, Catlab.WiringDiagrams

using ..Wiring, ..Poly
using ..Wiring: initial_state, AgentBox, update, name
using ...CategoricalAlgebra.CSets
import ..Poly: Mealy, apply_schedule, traj_res
using Catlab.CategoricalAlgebra.CSets: abstract_attributes, hasvar, attrtype_type

"""
This is a simple way of handling evaluation of diagrams which only works 
in the Maybe monad setting.
"""

# Partial map utilities 
#######################

id_pmap(s::StructACSet) = Span(abstract_attributes(s),abstract_attributes(s)) # the identity partial map
no_pmap(s1::StructACSet,s2::StructACSet) = Span(create.([s1,s2])...) # empty
tot_pmap(f::ACSetTransformation) = Span(id(dom(f)), f)

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
    !hasvar(codom(w)) || error("World state has variables $w")
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
function update_agent(t::Traj, idx::Int, a::ACSetTransformation; check=false)
  !check || is_natural(a) || error("Updating unnatural a")
  !hasvar(codom(a)) || error("World state has variables")
  A = dom(a)
  S = acset_schema(A)
  if idx < 0 error("Called update with negative index $idx") end
  if length(t) == 0 return idx==0 ? a : error("empty t w/ i=$idx") end
  comps = Dict{Any,Any}()
  for o in ob(S)
    comp = Int[]
    for aᵢ in parts(A,o)
      i = a[o](aᵢ)
      for j in idx+1:length(t)
        l,r = t[j].pmap
        p = preimage(l[o], i)
        if isempty(p) 
          return nothing 
        else 
          i = r[o](only(p))
        end
      end
      push!(comp, i)
    end
    comps[o] = comp
  end
  return only(homomorphisms(A, traj_res(t); initial=comps))
end
#     if i == length(t) # special case
#     codom(a) == codom(get_agent(t, i)) || error("BAD MATCH $i $a")
#     return a
#   end 
#   codom(a) == codom(left(t[i+1].pmap)) || error("BAD MATCH $i $a")
#   for j in i+1:length(t)
#     a = postcompose_partial(t[j].pmap, a)
#     if check && !is_natural(a) 
#       println("dom(a)"); show(stdout, "text/plain", dom(a))
#       println("codom(a)"); show(stdout, "text/plain", codom(a))
#       error("Updated unnatural a $(collect(pairs(components(a))))")
#     end
#     if isnothing(a) return nothing end 
#   end
#   codom(a) == traj_res(t) || error("Failed to postcompose $(codom(a))\n$(traj_res(t))")
#   return a 
# end


# Executing schedules 
#####################

Mealy(a::AgentBox, p::PMonad) = Mealy(update(a,p),p,initial_state(a), name(a))

function apply_schedule(s::Schedule,g::Any,t::PMonad=Maybe; kwargs...)
  typecheck(s)
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


# In-place interpreter
######################

# interpret a wiring diagram, with each box updating its state in place
function interpret(wd::WiringDiagram, g)
  ws = wires(wd)
  bs = boxes(wd)
  targets = Dict((w.source.box,w.source.port) => (w.target.box,w.target.port) for w in ws)
  boxstates = [Ref{Any}(initial_state(bs[i].value)) for i in 1:length(bs)]
  b = -2
  p = 1
  while true
    (nextb, inport) = targets[(b, p)]
    if nextb == -1
      return g
    end
    box = bs[nextb]
    g, p = update!(boxstates[nextb], box.value, g, inport)
    b = nextb
  end
end


function update!(state::Ref, boxdata, _cache, g, inport)
  # TODO
  println(typeof(boxdata))
  return nothing, 1
end

end # module 
