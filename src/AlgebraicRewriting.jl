module AlgebraicRewriting
using Reexport

include("categorical_algebra/CategoricalAlgebra.jl")
include("rewrite/Rewrite.jl")
include("incremental/Incremental.jl")
include("schedules/Schedules.jl")
include("analysis/Processes.jl")

@reexport using .CategoricalAlgebra
@reexport using .Rewrite
@reexport using .Incremental
@reexport using .Schedules



end # module
