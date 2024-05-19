"""
Incremental homomorphism search
"""
module Incremental 

using Reexport

include("Constraints.jl")
include("Algorithms.jl")
include("IncrementalHom.jl")
include("IncrementalCC.jl")
include("IncrementalSum.jl")
include("Cast.jl")

@reexport using .Constraints
@reexport using .Algorithms
@reexport using .IncrementalHom
@reexport using .IncrementalCC
@reexport using .IncrementalSum
@reexport using .Cast

end # module
