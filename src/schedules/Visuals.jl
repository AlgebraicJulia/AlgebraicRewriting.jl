module Visuals
export view_traj, graphviz

using ..Schedules
using Catlab.CategoricalAlgebra, Catlab.WiringDiagrams
using Requires



view_traj() = nothing

function __init__()
  @require Luxor = "ae8d54c2-7ccd-5906-9d76-62fc9837b5bc" include("view_traj.jl")
end


end # module
