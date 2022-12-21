module Schedules
export Schedule, ListSchedule, RuleSchedule, WhileSchedule, rewrite_schedule, RandomSchedule, apply_schedule, traj_res, ScheduleResult, rename_schedule, find_deps

using DataStructures, Random

using Catlab, Catlab.CategoricalAlgebra, Catlab.Graphs
using ..Rewrite
using ..Rewrite: rewrite_with_match
using Catlab.CategoricalAlgebra.DataMigrations: MigrationFunctor
import Base: map

abstract type Schedule end

(F::MigrationFunctor)(s::Schedule) = map(F, s)

struct ListSchedule <: Schedule
  rules::Vector{Schedule}
  name::Symbol
  ListSchedule(l::Vector{Schedule}, name=:list) =  new(l, name)
end

struct RuleSchedule{T} <: Schedule
  rule::Rule
  name::Symbol
  single::Bool # fire once vs for all matches in a random order
  match_prob::Float64 # probability for each match considered
  RuleSchedule(rule::Rule{T}, name=:_, single=false, prob=1.0) where T =
    new{T}(rule, name, single, 1.)
end

RuleSchedule{T}(pn::Pair{Symbol, Rule{T}}) where T  = RuleSchedule(pn[2], pn[1])

ListSchedule(rs::Vector{Rule}, name=:list) = ListSchedule(Schedule[
  RuleSchedule(r,Symbol("r$i")) for (i,r) in enumerate(rs)], name)

struct RandomSchedule <: Schedule
  rules::Vector{Rule}
  name::Symbol
end

struct WhileSchedule <: Schedule
  sch::Schedule
  name::Symbol
  cond::Function
  n::Int
  WhileSchedule(s::Schedule, name=:loop, cond=is_isomorphic, n=10) = new(s, name, cond, n)
end

WhileSchedule(r::Rule, name=:loop,cond=is_isomorphic,n=10) = WhileSchedule(RuleSchedule([r]), name, cond, n)

# Renaming schedules
function sub_symb(sym::Symbol, d::Dict{String, String})
  s = string(sym)
  for (k,v) in collect(d)
    s = replace(s, k=>v)
  end
  return Symbol(s)
end
rename_schedule(s::RuleSchedule{T}, n::Symbol) where T =
  RuleSchedule(s.rule, n, s.match_prob)
rename_schedule(s::ListSchedule, n::Symbol) = ListSchedule(s.rules, n)
rename_schedule(s::WhileSchedule, n::Symbol) = WhileSchedule(s.sch, n, s.cond)
rename_schedule(s::RuleSchedule{T}, n::Dict{String,String}) where T =
  RuleSchedule(s.rule, sub_symb(s.name, n), s.match_prob)
rename_schedule(s::ListSchedule, n::Dict{String,String}) =
  ListSchedule(Schedule[rename_schedule(r,n) for r in s.rules], sub_symb(s.name, n))
rename_schedule(s::WhileSchedule, n::Dict{String,String}) =
  WhileSchedule(rename_schedule(s.sch,n), sub_symb(s.name, n), s.cond)

# Mapping over schedules
map(F, s::RuleSchedule{T}) where T =  RuleSchedule(F(s.rule), s.name, s.match_prob)

map(F, s::ListSchedule) = ListSchedule(Schedule[map(F,s.rules)...], s.name)
map(F, s::RandomSchedule) =
  RandomSchedule(OrderedDict(s.name, [k=>F(v) for (k,v) in collect(s.rules)]))
map(F, s::WhileSchedule) = WhileSchedule(s.name, F(s.sch), s.cond, s.n)

struct TrajStep
  title::Symbol # rule that got applied
  G::StructACSet # current graph
  m::ACSetTransformation # match morphism that was used
  pmap::Span # partial map into this graph
end

function TrajStep(G::StructACSet)
  h=id(typeof(G)());
  TrajStep(:create, G, h, Span(h, create(G)))
end

const ScheduleResult = Vector{TrajStep}
traj_res(s::ScheduleResult) = last(s).G

"""apply schedule and return whether or not the input changed"""
function apply_schedule(s::ListSchedule; G=nothing, sr = nothing, random=false, verbose=false,kw...)::ScheduleResult
  sr = isnothing(sr) ? [TrajStep(G)] : sr
  f = random ? shuffle : identity
  if verbose println("applying sequence $(s.name)") end
  for r in f(s.rules)
    apply_schedule(r; sr=sr, random=random, verbose=verbose, kw...)
  end
  sr
end

function apply_schedule(r::RuleSchedule{T}; G=nothing, sr=nothing, random=false,
                        verbose=false, kw...)::ScheduleResult where T
  sr = isnothing(sr) ? [TrajStep(G)] : sr
  if verbose println("applying rule $(r.name)") end
  if r.single
    r_ = rewrite_with_match(r.rule, traj_res(sr); random=random, kw...);
    if !isnothing(r_)
      push!(sr, TrajStep(r.name, get_result(T, r_[2]), r_[1],
                              get_pmap(T, r_[2])))
    end
  else
    r_ = rewrite_sequential_maps(r.rule, traj_res(sr); random=random,
                                 prob=r.match_prob, verbose=verbose, kw...)
    for (m, s, g) in r_
      push!(sr, TrajStep(r.name, g, m, s))
    end
  end
  return sr
end

function apply_schedule(s::RandomSchedule; G=nothing, sr=nothing, kw...)::ScheduleResult
  sr = isnothing(sr) ? [TrajStep(G)] : sr

  for (n,r) in shuffle(s.rules)
    rewrite_schedule(r; sr=sr, kw...)
  end
  sr
end

function apply_schedule(s::WhileSchedule;
                        sr = nothing, G = nothing,
                        no_repeat::Bool=false, verbose::Bool=false, kw...)::ScheduleResult

  sr = isnothing(sr) ? [TrajStep(G)] : sr
  seen = Set(no_repeat ? [G] : [])
  for i in 1:s.n
    if verbose println("applying rule $(s.name) iter $i") end
    l = length(sr)
    prev = deepcopy(sr[end].G)
    apply_schedule(s.sch; sr=sr, verbose=verbose, kw...)
    if s.cond(prev, sr[end].G)
      return sr
    end

  end
  println("WARNING: hit nmax $(s.n) for WhileSchedule")
  return sr
end

rewrite_schedule(s::Schedule, G; kw...) = res(apply_schedule(s, G; kw...))


# Dependency analysis
#####################
"""
The relevant maps of an application of a single DPO rewrite.
"""
struct RWStep
  rule
  g
  match
  comatch
  function RWStep(r,g,m,c::T) where {T<:ACSetTransformation}
    codom(left(r)) == dom(m) || error("left(r)!=dom(m)")
    codom(right(r)) == dom(c) || error("right(r)!=dom(c)")
    codom(m) == codom(left(g)) || error("codom(m)!=codom(l)")
    codom(c) == codom(right(g)) || error("codom(c)!=codom(r)")
    new(r,g,m,c)
  end
end

function rw_steps(steps::AbstractVector)
  map(steps) do (r, m)
    _, kg, rh, kh = rewrite_match_maps(r, m)
    RWStep(Span(r.L, r.R), Span(kg, kh), m, rh)
  end
end

"""
For a concrete sequence of rewrites applications [a₁,a₂...aₙ], compute a poset
on the set of applications which reflects their casual connections, where a < b
mean that a must occur temporaly before b.
"""
function find_deps(seq::Vector{RWStep})
  # Construct a diagram which identifies parts across different rewrite steps
  n   = length(seq)
  ob₁ = [apex(s.g) for s in seq];
  ob₂ = codom.([left(first(seq).g), right.([x.g for x in seq])...])
  hom = vcat([[left(s.g), right(s.g)] for s in seq]...)
  src = vcat([fill(i,2) for i in 1:n]...); # [1, 1, 2, 2, 3, 3, ..., n, n]
  tgt = [1,vcat([fill(i,2) for i in 2:n]...)...,n+1] # [1, 2, 2, ..., n, n, n+1]
  hs  = collect(zip(hom, src, tgt))
  clim = colimit(BipartiteFreeDiagram(ob₁, ob₂, hs))
  clegs = legs(clim)
  
  # Identify which things are preserved, deleted, and created for each part
  Ob = objects(acset_schema(first(ob₁))) # objects in the schema 
  pres, del, cre = [Dict() for _ in 1:3]
  for o in Ob 
    pres[o], del[o], cre[o] = [[] for _ in 1:3]
    img(f) = Set(collect(f[o])) # the image of a map
    for (i,s) in enumerate(seq)
      push!(pres[o], img(left(s.rule) ⋅ s.match ⋅ clegs[i]))
      push!(del[o], setdiff(img(s.match ⋅ clegs[i]), pres[o][end]))
      push!(cre[o], setdiff(img(s.comatch ⋅ clegs[i+1]), pres[o][end]))
    end
  end 

  # Use the above to compute a presentation of a poset
  deps = Graph(length(seq))
  for o in Ob 
    for i in 1:n
      cre_i = cre[o][i]
      for j in filter(j->j!=i, 1:n)
        pres_del_j = pres[o][j] ∪ del[o][j]
        if !isempty(cre_i ∩ pres_del_j) && isempty(edges(deps, i, j))
          add_edge!(deps, i, j)
        end
      end
    end
  end
  return deps 
end

find_deps(s::AbstractVector) = s |> rw_steps |> find_deps


end # module
