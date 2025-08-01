"""
Specialized code for handling rewriting of ACSets with the identity monad
"""
module Eval 
export apply_schedule, rewrite_schedule, traj_res, interpret, interpret!

using Catlab, Catlab.CategoricalAlgebra, Catlab.WiringDiagrams

using ..Wiring, ..Poly
using ..Wiring: initial_state, AgentBox, name, update!
using ...CategoricalAlgebra.CSets
import ..Poly: Mealy, BTree, apply_schedule, traj_res
# using Catlab.CategoricalAlgebra: abstract_attributes, hasvar, attrtype_type


# In-place interpreter
######################

interpret(s::Schedule, g; kw...) = interpret(s.d, g; kw...)

interpret!(s::Schedule, g; kw...) = interpret!(s.d, g; kw...)

interpret!(wd::WiringDiagram, g::ACSet{<:MarkAsDeleted}; cat, kw...) = 
  interpret!(wd, create[cat](g); cat, kw...)

function interpret(wd::WiringDiagram, g::ACSet{<:MarkAsDeleted}; cat=nothing, kw...) 
  cat = isnothing(cat) ? infer_acset_cat(g) : cat
  interpret(wd, create[cat](g); cat, kw...)
end

"""interpret a wiring diagram, with each box updating its state in place"""
function interpret!(wd::WiringDiagram, 
                    g::ACSetTransformation; # {<:ACSet{<:MarkAsDeleted}}; TODO use MAD model
                    maxstep=1000000, cat)
  targets = Dict(map(wires(wd)) do w 
    (w.source.box, w.source.port) => (w.target.box,w.target.port) 
  end)
  boxstates = [Ref{Any}(initial_state(boxes(wd)[i].value)) for i in 1:length(boxes(wd))]
  b, p, msg = input_id(wd), 1, ""
  for counter in 0:maxstep
    (nextb, inport) = targets[(b, p)]
    @debug "$counter NEXT: $nextb#$inport $(wd.diagram[b, :value])"
    nextb == -1 && return g
    box = boxes(wd)[nextb]
    b, (g, p, msg) = nextb, update!(boxstates[nextb], box.value, g, inport; cat)
  end
  @warn "Exceeded maximum number of steps"
  g
end

"""Interpret a wiring diagram, recording the trajectory taken"""
function interpret(wd::WiringDiagram, 
                   world::ACSetTransformation; # {<:ACSet{<:MarkAsDeleted}}; USE MAD model
                   maxstep=1000000, cat=nothing)
  cat = isnothing(cat) ? infer_acset_cat(world) : cat
  targets = Dict(map(wires(wd)) do w 
    (w.source.box, w.source.port) => (w.target.box,w.target.port) 
  end)
  boxstates = [Ref{Any}(initial_state(boxes(wd)[i].value)) 
               for i in 1:length(boxes(wd))]
  b, p, msg =  input_id(wd), 1, "start"
  traj = Tuple{ACSetTransformation,Vector{Tuple{Int,Int,String}}}[]
  for counter in 0:maxstep
    if isempty(traj) || first(last(traj)) != world
      push!(traj, (deepcopy(world), [(b, p, msg)]))
    elseif !isempty(traj) 
      push!(last(last(traj)), (b, p, msg))
    end
    (nextb, inport) = targets[(b, p)]
    nextb == -1 && return traj
    box = boxes(wd)[nextb]
    @debug "$counter NEXT: $nextb#$inport $(box.value)"
    b, (world, p, msg) = nextb, update!(boxstates[nextb], box.value, world, inport; cat)
  end
  @warn "Exceeded maximum number of steps"
  return traj
end

end # module 
