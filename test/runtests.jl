using Test

using AlgebraicRewriting
@test length(methods(view_traj)) == 1
using Luxor
@test length(methods(view_traj)) > 1

@testset "Lotka Volterra" begin
  include("../docs/src/lotka_volterra.jl") # this shouldn't crash
end

# Background 
############

@testset "StructuredCospans" begin
  include("categorical_algebra/StructuredCospans.jl")
end

@testset "CSets" begin
  include("categorical_algebra/CSets.jl")
end

@testset "FinSets" begin
  include("categorical_algebra/FinSets.jl")
end

@testset "PartialMap" begin
  include("categorical_algebra/PartialMap.jl")
end

@testset "Constraints" begin
  include("rewrite/Constraints.jl")
end

# Rewriting flavors
###################
@testset "DPO" begin
  include("rewrite/DPO.jl")
end

@testset "SPO" begin
  include("rewrite/SPO.jl")
end

@testset "SqPO" begin
  include("rewrite/SqPO.jl")
end

@testset "PBPO" begin
  include("rewrite/PBPO.jl")
end

# Schedules 
##########

@testset "Schedules" begin
  include("schedules/Poly.jl")
end

@testset "Schedules" begin
  include("schedules/Eval.jl")
end
