using Test

# Test package extension loading
using AlgebraicRewriting
@test length(methods(Rule)) == 1

# using DataMigrations # @test length(methods(Rule)) > 1

module Demos 
  include("../docs/literate/full_demo.jl")
  include("../docs/literate/lotka_volterra.jl")
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

# Wait until DataMigrations is migrated to Catlab 0.17
# @testset "Representable" begin
#   include("rewrite/Representable.jl")
# end

@testset "Inplace" begin
  include("rewrite/Inplace.jl")
end

# Incremental 
##############
@testset "Incremental" begin
    include("incremental/runtests.jl")
end


# Schedules 
##########

@testset "Schedules: Poly" begin
  include("schedules/Poly.jl")
end

@testset "Schedules: Eval" begin
  include("schedules/Eval.jl")
end
