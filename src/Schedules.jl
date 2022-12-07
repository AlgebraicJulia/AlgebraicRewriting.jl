module Schedules
export NestedDWD, inner, outer, 
       NPorts, ListSchedule, RuleSchedule, const_cond, if_cond,
       no_match, apply_schedule, uniform, merge_wires,
       ScheduleResult
      #  Schedule, WhileSchedule, 
      #  rewrite_schedule, RandomSchedule, traj_res, 
      #  , rename_schedule

using DataStructures, Random

using Catlab, Catlab.CategoricalAlgebra, Catlab.WiringDiagrams, Catlab.Theories
using ..Rewrite
using ..Rewrite: rewrite_with_match, get_matches
using Catlab.CategoricalAlgebra.DataMigrations: MigrationFunctor
using Catlab.WiringDiagrams.DirectedWiringDiagrams: tgt_box, in_tgt_box

import Base: map
import Catlab.WiringDiagrams: ocompose
import Catlab.Graphics: to_graphviz, LeftToRight
import Catlab.Theories: dom, codom, id, compose, ⋅, ∘, otimes, ⊗, munit, braid, σ

struct NestedDWD 
  outer::WiringDiagram
  inner::Vector{NestedDWD}
  NestedDWD(o::WiringDiagram, i = NestedDWD[]) = new(o, i)
end 
outer(d::NestedDWD) = d.outer 
inner(d::NestedDWD) = d.inner

function NestedDWD(b::Box) 
  wd = WiringDiagram(b.input_ports, b.output_ports)
  add_box!(wd,b)
  add_wires!(wd, Pair[[(input_id(wd),i)=>(1,i) for i in 1:length(b.input_ports)]...,
                  [(1,i)=>(output_id(wd),i) for i in 1:length(b.output_ports)]...])
  NestedDWD(wd)
end
struct NPorts 
  p::Ports 
  NPorts(n::Int) = new(Ports(fill(:X, n)))
  NPorts(p::Ports) = new(p)
end 

@instance ThSymmetricMonoidalCategory{NPorts, NestedDWD} begin
  @import dom, codom

  id(A::NPorts) = NestedDWD(id(A.p))

  function compose(f::NestedDWD, g::NestedDWD)
    NestedDWD(f.outer⋅g.outer,vcat(f.inner, g.inner))
  end

  otimes(A::NPorts, B::NPorts) = NPorts(A.p ⊗ B.p)
  munit(::Type{NPorts}) = NPorts(0)

  otimes(f::NestedDWD, g::NestedDWD) = NestedDWD(f.outer⊗g.outer,vcat(f.inner, g.inner))

  braid(A::NPorts, B::NPorts) = NPorts(braid(A.p,B.p))
end

struct NamedRule
  name::String 
  rule::Rule 
end 
Base.string(c::NamedRule) = c.name

"""
A function ACSet -> ℝⁿ which weights probability for n outports, conditional on 
the status of an ACSet.
"""
struct Condition 
  name::String 
  fun::Function
  n::Int
end

Base.string(c::Condition) = c.name

const_cond(v::Vector{Float64};name=nothing) = 
  Box(Condition(isnothing(name) ? "const $v" : name, _->v,length(v)), 
      [:X],fill(:X,length(v)))
uniform(n::Int) = const_cond(fill(1/n,n); name="uniform")

if_cond(name::String, boolfun::Function) = 
  Box(Condition(name, x->boolfun(x) ? [1,0] : [0,1], 2),[:X],[:X,:X])
has_match(rulename::String, r::Rule) = 
  if_cond("Can match $rulename", x->!isempty(get_matches(r,x)))

function merge_wires(n::Int)
  wd = WiringDiagram(fill(:X,n),[:X])
  add_wires!(wd, Pair[(input_id(wd),i)=>(output_id(wd),1) for i in 1:n])
  return NestedDWD(wd)
end

function ocompose(d::NestedDWD)
  if isempty(d.inner) return d end 
  NestedDWD(ocompose(d.outer, [ocompose(i).outer for i in d.inner]))
end 

to_graphviz(d::NestedDWD; orientation=LeftToRight, kw...) = to_graphviz(ocompose(d).outer; orientation=orientation, kw...)

apply_schedule_step(s::NestedDWD, g::StructACSet, w::Int) = 
  apply_schedule_step(ocompose(s).outer, g, w)

function apply_schedule_step(s::WiringDiagram, g::StructACSet, box::Int)
  btype = s.diagram[box, :value]
  if btype isa Condition 
    dist = btype.fun(g)
    return findfirst(q -> q > rand(), cumsum(dist) ./ sum(dist))
  elseif btype isa NamedRule 
    return rewrite_with_match(btype.rule, g)
  else 
    error("Unknown semantics for $btype")
  end
end

struct TrajStep
  title::String # rule that got applied
  port::Pair{Int,Int}
  G::StructACSet # current graph
  m::Union{Nothing,ACSetTransformation} # match morphism that was used
  pmap::Union{Nothing,Span} # partial map into this graph
  TrajStep(t,p,g,m=nothing,pmap=nothing) = new(t,p,g,m,pmap)
end

function TrajStep(G::StructACSet)
  h=id(typeof(G)());
  TrajStep(:create, G, h, Span(h, create(G)))
end

const ScheduleResult = Vector{TrajStep}
traj_res(s::ScheduleResult) = last(s).G

function apply_schedule(s::WiringDiagram,g::StructACSet, b::Int=0,p::Int=0; 
                        steps::Int=-1)::ScheduleResult
  res = TrajStep[]
  b,p = (b,p) == (0,0) ? (input_id(s), 1) : (b, p)
    
  while steps!=0 
    steps -= 1
    box = only(out_wires(s, Port(b,OutputPort,p))).target.box
    if box == output_id(s) return res end 
    boxval = s.diagram[box, :value]

    stepres = apply_schedule_step(s, g, box)
    if isnothing(stepres) # we failed to match a rule box 
      (b,p) = (box, 1)
    elseif stepres isa Int # we applied the condition and got an outport
      (b,p) = (box, stepres)
      push!(res, TrajStep(boxval.name, b=>p, g, nothing, Span(id(g), id(g))))
    else # we have a rewrite result 
      (b,p) = (box, 1)
      match, maps = stepres
      g, pmap = [f(ruletype(boxval.rule), maps) for f in [get_result, get_pmap]]
      push!(res,TrajStep(boxval.name, b=>p, g, match, pmap))
    end
  end 
  return res
end

function RuleSchedule(n::String, r::Rule; loop::Bool=false)
  wd = WiringDiagram([:X],[:X])
  add_box!(wd,Box(NamedRule(n,r), [:X],[:X]))
  add_wires!(wd, Pair[(input_id(wd),1)=>(1,1),(1,1)=>(output_id(wd),1)])
  if loop
    rem_wire!(wd,only(in_wires(wd, output_id(wd))))
    add_box!(wd, has_match(n,r))
    add_wires!(wd, Pair[(1,1)=>(2,1), (2,1)=>(1,1), (2,2)=>(output_id(wd),1)])
  end
  NestedDWD(wd)
end


if false 
  # abstract type Schedule end

  # (F::MigrationFunctor)(s::Schedule) = map(F, s)

  # struct ListSchedule <: Schedule
  #   rules::Vector{Schedule}
  #   name::Symbol
  #   ListSchedule(l::Vector{Schedule}, name=:list) =  new(l, name)
  # end

  # struct RuleSchedule{T} <: Schedule
  #   rule::Rule
  #   name::Symbol
  #   single::Bool # fire once vs for all matches in a random order
  #   match_prob::Float64 # probability for each match considered
  #   RuleSchedule(rule::Rule{T}, name=:_, single=false, prob=1.0) where T =
  #     new{T}(rule, name, single, 1.)
  # end

  # RuleSchedule{T}(pn::Pair{Symbol, Rule{T}}) where T  = RuleSchedule(pn[2], pn[1])

  # ListSchedule(rs::Vector{Rule}, name=:list) = ListSchedule(Schedule[
  #   RuleSchedule(r,Symbol("r$i")) for (i,r) in enumerate(rs)], name)

  # struct RandomSchedule <: Schedule
  #   rules::Vector{Rule}
  #   name::Symbol
  # end

  # struct WhileSchedule <: Schedule
  #   sch::Schedule
  #   name::Symbol
  #   cond::Function
  #   n::Int
  #   WhileSchedule(s::Schedule, name=:loop, cond=is_isomorphic, n=10) = new(s, name, cond, n)
  # end

  # WhileSchedule(r::Rule, name=:loop,cond=is_isomorphic,n=10) = WhileSchedule(RuleSchedule([r]), name, cond, n)

  # # Renaming schedules
  # function sub_symb(sym::Symbol, d::Dict{String, String})
  #   s = string(sym)
  #   for (k,v) in collect(d)
  #     s = replace(s, k=>v)
  #   end
  #   return Symbol(s)
  # end
  # rename_schedule(s::RuleSchedule{T}, n::Symbol) where T =
  #   RuleSchedule(s.rule, n, s.match_prob)
  # rename_schedule(s::ListSchedule, n::Symbol) = ListSchedule(s.rules, n)
  # rename_schedule(s::WhileSchedule, n::Symbol) = WhileSchedule(s.sch, n, s.cond)
  # rename_schedule(s::RuleSchedule{T}, n::Dict{String,String}) where T =
  #   RuleSchedule(s.rule, sub_symb(s.name, n), s.match_prob)
  # rename_schedule(s::ListSchedule, n::Dict{String,String}) =
  #   ListSchedule(Schedule[rename_schedule(r,n) for r in s.rules], sub_symb(s.name, n))
  # rename_schedule(s::WhileSchedule, n::Dict{String,String}) =
  #   WhileSchedule(rename_schedule(s.sch,n), sub_symb(s.name, n), s.cond)

  # # Mapping over schedules
  # map(F, s::RuleSchedule{T}) where T =  RuleSchedule(F(s.rule), s.name, s.match_prob)

  # map(F, s::ListSchedule) = ListSchedule(Schedule[map(F,s.rules)...], s.name)
  # map(F, s::RandomSchedule) =
  #   RandomSchedule(OrderedDict(s.name, [k=>F(v) for (k,v) in collect(s.rules)]))
  # map(F, s::WhileSchedule) = WhileSchedule(s.name, F(s.sch), s.cond, s.n)


  # """apply schedule and return whether or not the input changed"""
  # function apply_schedule(s::ListSchedule; G=nothing, sr = nothing, random=false, verbose=false,kw...)::ScheduleResult
  #   sr = isnothing(sr) ? [TrajStep(G)] : sr
  #   f = random ? shuffle : identity
  #   if verbose println("applying sequence $(s.name)") end
  #   for r in f(s.rules)
  #     apply_schedule(r; sr=sr, random=random, verbose=verbose, kw...)
  #   end
  #   sr
  # end

  # function apply_schedule(r::RuleSchedule{T}; G=nothing, sr=nothing, random=false,
  #                         verbose=false, kw...)::ScheduleResult where T
  #   sr = isnothing(sr) ? [TrajStep(G)] : sr
  #   if verbose println("applying rule $(r.name)") end
  #   if r.single
  #     r_ = rewrite_with_match(r.rule, traj_res(sr); random=random, kw...);
  #     if !isnothing(r_)
  #       push!(sr, TrajStep(r.name, get_result(T, r_[2]), r_[1],
  #                               get_pmap(T, r_[2])))
  #     end
  #   else
  #     r_ = rewrite_sequential_maps(r.rule, traj_res(sr); random=random,
  #                                 prob=r.match_prob, verbose=verbose, kw...)
  #     for (m, s, g) in r_
  #       push!(sr, TrajStep(r.name, g, m, s))
  #     end
  #   end
  #   return sr
  # end

  # function apply_schedule(s::RandomSchedule; G=nothing, sr=nothing, kw...)::ScheduleResult
  #   sr = isnothing(sr) ? [TrajStep(G)] : sr

  #   for (n,r) in shuffle(s.rules)
  #     rewrite_schedule(r; sr=sr, kw...)
  #   end
  #   sr
  # end

  # function apply_schedule(s::WhileSchedule;
  #                         sr = nothing, G = nothing,
  #                         no_repeat::Bool=false, verbose::Bool=false, kw...)::ScheduleResult

  #   sr = isnothing(sr) ? [TrajStep(G)] : sr
  #   seen = Set(no_repeat ? [G] : [])
  #   for i in 1:s.n
  #     if verbose println("applying rule $(s.name) iter $i") end
  #     l = length(sr)
  #     prev = deepcopy(sr[end].G)
  #     apply_schedule(s.sch; sr=sr, verbose=verbose, kw...)
  #     if s.cond(prev, sr[end].G)
  #       return sr
  #     end

  #   end
  #   println("WARNING: hit nmax $(s.n) for WhileSchedule")
  #   return sr
  # end

  # rewrite_schedule(s::Schedule, G; kw...) = res(apply_schedule(s, G; kw...))
end 

end # module