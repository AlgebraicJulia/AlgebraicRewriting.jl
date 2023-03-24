module Visuals
export view_traj, graphviz, view_sched

using ..Schedules
using ..Schedules.Wiring: wnames, wire_vals, color, Schedule
using Catlab.CategoricalAlgebra, Catlab.WiringDiagrams, Catlab.Graphics
using Catlab.WiringDiagrams.DirectedWiringDiagrams: out_port_id
using Requires



view_traj() = nothing

function __init__()
  @require Luxor = "ae8d54c2-7ccd-5906-9d76-62fc9837b5bc" include("view_traj.jl")
end


function view_sched(sched_::Schedule; name="",source=nothing, target=nothing, names=nothing)
  sched = WiringDiagram([], [])
  copy_parts!(sched.diagram,sched_.d.diagram)


  for (i, (s,t,wval,sval,tval)) in enumerate(wnames)
    for (w,vs) in enumerate(wire_vals(sched, i)) 
      n = isnothing(names) ? "" : join(
        unique([v isa String ? v : get(names,v,"?") for v in vs])," | ")
      set_subpart!(sched.diagram, w,  wval, n)
      set_subpart!(sched.diagram, sched.diagram[w,s], sval, n)
      set_subpart!(sched.diagram, sched.diagram[w,t], tval, n)

    end
  end
  if !isnothing(source)
    if source.box == input_id(sched) 
      sched.diagram[source.port, :outer_in_port_type] *= "→"
    else 
      sched.diagram[out_port_id(sched, source), :out_port_type] *= "→"
    end
    sched.diagram[out_port_id(sched, target), :out_port_type] *= "←"
  end
  return to_graphviz(sched; labels=true, 
    graph_attrs=Dict(:label=>name, :labelloc=>"t"),
    node_colors=Dict(i=>color(b.value) for (i,b) in enumerate(boxes(sched))))
end

end # module
