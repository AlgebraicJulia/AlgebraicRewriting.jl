using BenchmarkTools

const SUITE = BenchmarkGroup()

module BenchmarkAgents
  include("Agents.jl")
end


SUITE["Agents"] = BenchmarkAgents.SUITE
