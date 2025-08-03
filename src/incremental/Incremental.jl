"""
Incremental homomorphism search
"""
module Incremental 

using Reexport

include("Algorithms.jl")
include("IHSData.jl")
include("IHSAccess.jl")
include("IHSModify.jl")
include("IHSRewrite.jl")


@reexport using .Algorithms
@reexport using .IHSData
@reexport using .IHSAccess
@reexport using .IHSModify
@reexport using .IHSRewrite

end # module
