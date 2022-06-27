module Schedules
export ListSchedule, WhileSchedule, rewrite_schedule, RandomSchedule, apply_schedule, res, ScheduleResult

using DataStructures, Random

using Catlab, Catlab.CategoricalAlgebra
using ..Rewrite
using ..Rewrite: rewrite_with_match

abstract type Schedule end

struct ListSchedule <: Schedule
  rules::OrderedDict{Symbol, Rule}
  ListSchedule(l::Vector{Pair{Symbol, Rule}})=  new(OrderedDict(l))
end

ListSchedule(rs::Vector{Rule}) = ListSchedule([
  Symbol("r$i")=>r for (i,r) in enumerate(rs)])

struct RandomSchedule <: Schedule
    rules::Vector{Rule}
end
struct WhileSchedule <: Schedule
    sch::Schedule
end

mutable struct ScheduleResult
  traj::Vector{Tuple{Symbol, ACSetTransformation, StructACSet}}
end
res(s::ScheduleResult) = last(last(s.traj))

WhileSchedule(r::Rule) = WhileSchedule(ListSchedule([r]))


"""apply schedule and return whether or not the input changed"""
function apply_schedule(s::ListSchedule, G; sr = nothing, random=false,kw...)
  sr = isnothing(sr) ? ScheduleResult([(:create, create(G), G)]) : sr
  f = random ? shuffle : identity
  for (n,r) in f(collect(s.rules))
    G_ = rewrite_with_match(r, res(sr); random=random, kw...)
    if !isnothing(G_)
      push!(sr.traj, (n, G_[2], G_[1]))
    end
  end
  return sr
end

function apply_schedule(s::RandomSchedule, G; kw...)
  for (n,r) in shuffle(s.rules)
    G_ = rewrite(r, G; kw...)
    if !isnothing(G_)
      push!(sr.traj, (n, G_[2], G_[1]))
    end
  end
  return G => changed
end

function apply_schedule(s::WhileSchedule, G;
                        sr = nothing,
                        no_repeat::Bool=false, kw...)

  nmax = 10
  sr = isnothing(sr) ? ScheduleResult([(:create, create(G), G)]) : sr
  seen = Set(no_repeat ? [G] : [])
  for _ in 1:nmax
    l = length(sr.traj)
    apply_schedule(s.sch, res(sr); seen=seen, sr=sr, kw...)
    if length(sr.traj) == l
      return sr
    end
    if no_repeat seen = Set(last.(sr.traj)) end
  end
  println("WARNING: hit nmax $nmax for WhileSchedule")
  sr
end

rewrite_schedule(s::Schedule, G; kw...) = res(apply_schedule(s, G; kw...))

end # module