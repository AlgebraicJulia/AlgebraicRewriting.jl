module Visuals
export view_traj, graphviz, view_sched

using ..Schedules
using ..Schedules.Wiring: wnames, wire_vals, color, Schedule, Names
using Catlab.CategoricalAlgebra, Catlab.WiringDiagrams, Catlab.Graphics
using Catlab.WiringDiagrams.DirectedWiringDiagrams: out_port_id


# Visualization
###############
"""
Visualize a trajectory with two views: one showing the current position within 
the schedule, and the other showing the world state.

Viewer must be a function which accepts a path and writes an image to it.
"""
function view_traj(sched_::Schedule, rG::AbstractVector, viewer; 
                                      out="traj", agent=false, names=nothing)
  if isdir(out) # clear old dir
    for fi in filter(x->length(x)>4 && x[end-3:end] == ".png",  readdir(out))
      rm(joinpath(out,fi))
    end
  else
    mkdir(out)
  end
  expanded = []
  for (k, vs) in rG, (b, p, m) in vs 
    push!(expanded, (k, Port(b, OutputPort, p), m))
  end
  for n in 1:length(expanded)-1
    view_traj(sched_, expanded, viewer, n; out=out, agent=agent,names=names)
  end
end
 
"""
If `agent` is true, then the viewer function should operate on 
ACSetTransformations, rather than ACSets.
"""
function view_traj(sched_::Schedule, traj::AbstractVector, viewer, n::Int; 
                   out="traj", agent=false, names=nothing)
  (Gₙ, portₙ, _), (Gₙ′, portₙ′, name) = traj[n], traj[n+1]
  sched = view_sched(sched_; name, source=portₙ, target=portₙ′, names=names)
  open("$out/$(n)_schedule.svg", "w") do io
    show(io,"image/svg+xml",sched)
  end
  gs = (agent ? identity : codom).([Gₙ, Gₙ′])
  viewer(gs[1], "$out/$(n)_in.svg")
  viewer(gs[2], "$out/$(n)_out.svg")
end

function view_sched(sched_::Schedule; name="",source=nothing, target=nothing, 
                    names=nothing)
  sched = WiringDiagram([], [])
  copy_parts!(sched.diagram,sched_.d.diagram)

  for (i, (s,t,wval,sval,tval)) in enumerate(wnames)
    for (w,vs) in enumerate(wire_vals(sched, i)) 
      n = isnothing(names) ? "" : join(
        unique([v isa String ? v : names[v] for v in vs])," | ")
      set_subpart!(sched.diagram, w,  wval, n)
      set_subpart!(sched.diagram, sched.diagram[w,s], sval, n)
      set_subpart!(sched.diagram, sched.diagram[w,t], tval, n)

    end
  end
  if !isnothing(source)
    if source.box == input_id(sched) 
      sched.diagram[source.port, :outer_in_port_type] *= " (in)"
    else 
      sched.diagram[out_port_id(sched, source), :out_port_type] *= " (in)"
    end
    if !isnothing(target)
      sched.diagram[out_port_id(sched, target), :out_port_type] *= " (out)"
    end
  end
  return to_graphviz(sched; labels=true, 
    graph_attrs=Dict(:label=>name, :labelloc=>"t"),
    node_colors=Dict(i=>color(b.value) for (i,b) in enumerate(boxes(sched))))
end

end # module
