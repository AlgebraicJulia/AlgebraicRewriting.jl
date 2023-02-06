module CategoricalAlgebra


"""
Functionality that is of more general use than just rewriting
"""

using Reexport

include("FinSets.jl")
include("CSets.jl")
include("StructuredCospans.jl")
include("PartialMap.jl")

@reexport using .FinSets
@reexport using .CSets
@reexport using .StructuredCospans
@reexport using .PartialMap

end # module
