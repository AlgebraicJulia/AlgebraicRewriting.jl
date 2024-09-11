using Test

# Test package extension loading
using AlgebraicRewriting
@test length(methods(view_traj)) == 1
@test length(methods(Rule)) == 1
using Luxor
@test length(methods(view_traj)) > 1
using DataMigrations
@test length(methods(Rule)) > 1

# Demos
#######

@testset "Full Demo" begin
  include("../docs/literate/full_demo.jl")
end

@testset "Lotka Volterra" begin
  include("../docs/literate/lotka_volterra.jl")
end

@testset "Game of Life" begin
  include("../docs/literate/game_of_life.jl")
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

@testset "CoNeg" begin
  include("rewrite/CoNeg.jl")
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

@testset "Representable" begin
  include("rewrite/Representable.jl")
end

@testset "Inplace" begin
  include("rewrite/Inplace.jl")
end

# Schedules 
##########

@testset "Schedules: Poly" begin
  include("schedules/Poly.jl")
end

@testset "Schedules: Eval" begin
  include("schedules/Eval.jl")
end

# Incremental hom search
########################

@testset "Incremental" begin
  include("incremental/Incremental.jl")
end
