module AlgebraicRewriting
using Reexport

include("Variables.jl")
include("FinSets.jl")
include("Search.jl")
include("CSets.jl")
include("StructuredCospans.jl")
include("PartialMap.jl")
include("Rewrite.jl")
include("Inplace.jl")
include("Schedules.jl")
include("Visuals.jl")

@reexport using .Variables
@reexport using .FinSets
@reexport using .Search
@reexport using .CSets
@reexport using .StructuredCospans
@reexport using .PartialMap
@reexport using .Rewrite
@reexport using .Inplace
@reexport using .Schedules
@reexport using .Visuals



end # module
