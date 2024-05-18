"""
Incremental homomorphism search
"""
module Incremental 
# export IncHomSet, rewrite!, matches

# using ..Rewrite
# using ..Rewrite.Utils: get_result, get_rmap, get_pmap, get_expr_binding_map
# using ..CategoricalAlgebra.CSets: invert_iso, extend_morphism
# import ..Rewrite: rewrite!, can_match

# using StructEquality
# using Catlab
# import Catlab: universal
# using Catlab.CategoricalAlgebra.CSets: ACSetColimit
# using Catlab.CategoricalAlgebra.HomSearch: total_parts

# const × = Iterators.product

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
