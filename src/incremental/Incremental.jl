"""
Incremental homomorphism search
"""
module Incremental 

using Reexport

include("Algorithms.jl")
include("IncrementalConstraints.jl")
include("IncrementalHom.jl")
include("IncrementalCC.jl")
include("IncrementalSum.jl")
include("Cast.jl")

@reexport using .IncrementalConstraints
@reexport using .Algorithms
@reexport using .IncrementalHom
@reexport using .IncrementalCC
@reexport using .IncrementalSum
@reexport using .Cast

end # module
