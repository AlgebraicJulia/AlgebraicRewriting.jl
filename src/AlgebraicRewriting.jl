module AlgebraicRewriting
using Reexport

include("categorical_algebra/CategoricalAlgebra.jl")
include("rewrite/Rewrite.jl")
include("schedules/Schedules.jl")

@reexport using .CategoricalAlgebra
@reexport using .Rewrite
@reexport using .Schedules



end # module
