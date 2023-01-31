module Visuals
export view_traj, graphviz

using ..Schedules
using Catlab.CategoricalAlgebra, Catlab.WiringDiagrams
using Catlab.Graphics: to_graphviz
using Requires

graphviz(wd::WiringDiagram; kw...) = to_graphviz(wd; 
  node_colors=Dict(i=>color(b.value) for (i,b) in enumerate(boxes(wd))), kw...)


view_traj() = nothing

function __init__()
  @require Interact = "c601a237-2ae4-5e1e-952c-7a85b0c7eef1" include("view_traj.jl")
end


end # module
