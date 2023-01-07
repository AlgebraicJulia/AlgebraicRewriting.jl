module AlgebraicRewriting
using Reexport

include("categorical_algebra/CategoricalAlgebra.jl")
include("rewrite/Rewrite.jl")
include("Schedules.jl")
include("Visuals.jl")

@reexport using .CategoricalAlgebra
@reexport using .Rewrite
@reexport using .Schedules
@reexport using .Visuals



end # module
