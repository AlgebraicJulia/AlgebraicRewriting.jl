module Visuals
export view_traj

using ..Schedules
using Catlab.CategoricalAlgebra
using Requires

view_traj() = nothing

function __init__()
  @require Interact = "c601a237-2ae4-5e1e-952c-7a85b0c7eef1" include("view_traj.jl")
end


end # module
