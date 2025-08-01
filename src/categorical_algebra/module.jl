module CategoricalAlgebra


"""
Functionality that is of more general use than just rewriting
"""

using Reexport

include("Theories.jl")

include("FinSets.jl")
include("CSets.jl")
include("StructuredCospans.jl")
include("PartialMap.jl")
include("SliceCats.jl")

@reexport using .Theories
@reexport using .FinSets
@reexport using .CSets
@reexport using .StructuredCospans
@reexport using .PartialMap

end # module
