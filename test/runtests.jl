using Test

include("../docs/src/lotka_volterra.jl") # this shouldn't crash


@testset "Variables" begin
  include("Variables.jl")
end

@testset "Schedule" begin
  include("Schedule.jl")
end

@testset "StructuredCospans" begin
  include("StructuredCospans.jl")
end

@testset "CSets" begin
  include("CSets.jl")
end

@testset "FinSets" begin
  include("FinSets.jl")
end

@testset "PartialMap" begin
  include("PartialMap.jl")
end

@testset "Rewrite" begin
  include("Rewrite.jl")
end

@testset "Search" begin
  include("Search.jl")
end
