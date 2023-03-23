module Wiring
export Schedule,Traj, TrajStep, mk_sched, typecheck, merge_wires, 
       singleton, traj_res, traj_agent, view_sched

using Catlab, Catlab.CategoricalAlgebra, Catlab.WiringDiagrams, Catlab.Programs,
      Catlab.Theories
import Catlab.WiringDiagrams.DirectedWiringDiagrams: input_ports,output_ports
import Catlab.Theories: Ob,Hom,id, create, compose, otimes, ⋅, ⊗, ∇,□, trace, munit, braid, dom, codom, mmerge
using ...CategoricalAlgebra.CSets
using ...CategoricalAlgebra.CSets: abstract
using ..Theories: TM, ThTracedMonoidalWithBidiagonals


"""
The true "primitive" is the Scientist category, which works for morphisms of any 
level of generality (e.g. composites). However, our effective primitives are: 
  RuleApp, Conditional, Query, Weaken/Strengthen Agent, and Initialize.

There are also higher level patterns built from these generating morphisms.
"""

# String utilities 
##################
"""Visualize the data of a CSet homomorphism"""
str_hom(m::ACSetTransformation) = join([
  "$k: $(collect(c))" for (k,c) in pairs(components(m))
  if !isempty(collect(c))], '\n')

# Partial map utilities 
#######################

id_pmap(s::StructACSet) = Span(abstract(s),abstract(s)) # the identity partial map
no_pmap(s1::StructACSet,s2::StructACSet) = Span(create.([s1,s2])...) # empty
tot_pmap(f::ACSetTransformation) = Span(id(dom(f)), f)

noattr(s::StructACSet{S}) where S = all(a->nparts(s,a) == 0, attrtypes(S))
noattr(s::ACSetTransformation) = noattr(codom(s))

# General wiring diagram utilities
###################################

"""
Make a wiring diagram with ob/hom generators using @program macro

TODO double check that this does not introduce any wire splitting.
"""
function mk_sched(t_args::NamedTuple,args::NamedTuple,
                  kw::Union{NamedTuple,AbstractDict}, wd::Expr)
  n_trace=length(t_args)
  os = Dict(k=>v for (k,v) in collect(pairs(kw)) if v isa StructACSet)
  hs = Dict(k=>(v isa AgentBox ? singleton(v) : v) for (k,v) in collect(pairs(kw))
            if v isa Union{Schedule,AgentBox})
  P = Presentation(TM)
  os_ = Dict(v=>add_generator!(P, Ob(TM,k)) for (k,v) in collect(os))
  # for (k,v) in collect(os) 
  #   if haskey(os,v)
  #     sym_dict[k] = Symbol(os[v])
  #   else
  #     os_[v]=add_generator!(P, Ob(TM, k))
  #   end
  # end
  for (k,v) in collect(hs)
    i = (isempty(input_ports(v)) 
        ? munit(TM.Ob) 
        : otimes([os_[ip] for ip in input_ports(v)]))
    o = (isempty(output_ports(v)) ? munit(TM.Ob) : otimes([os_[op] for op in output_ports(v)]))
    add_generator!(P, Hom(k, i, o))
  end
  args_ = Expr(:tuple,[Expr(Symbol("::"), k,v) for (k,v) in pairs(merge(t_args,args))]...)

  tmp = parse_wiring_diagram(P, args_, wd)
  tmpx = to_hom_expr(TM, tmp)
  
  Xports = Ports{ThTracedMonoidalWithBidiagonals}(input_ports(tmp)[1:n_trace])
  new_d = trace(Xports, tmp)

  X = n_trace == 0 ? munit(TM.Ob) : otimes(dom(tmpx).args[1:n_trace])
  A = n_trace == length(dom(tmpx).args) ? munit(TM.Ob) : otimes([Ob(TM,x) for x in dom(tmpx).args[n_trace+1:end]])
  B = n_trace == length(codom(tmpx).args) ? munit(TM.Ob) : otimes([Ob(TM,x) for x in codom(tmpx).args[n_trace+1:end]])
  new_x = trace(X, A,B, tmpx)

  function ob_map(expr)
    sxpr = Symbol(expr)
    haskey(os, sxpr) ? Ob(TM, os[sxpr]) : expr 
  end
  function hom_map(expr)
    sxpr = Symbol(expr)
    haskey(hs, sxpr) ? hs[sxpr].x : expr   
  end

  newer_x = functor((TM.Ob,TM.Hom),new_x, terms=Dict(:Ob=>ob_map, :Hom=>hom_map))
  
  sub = ocompose(new_d, [hs[Symbol(b.value)].d for b in boxes(new_d)])
  sub.diagram[:wire_value] = nothing
  for x in Symbol.(["$(x)_port_type" for x in [:outer_in,:outer_out,]])
    sub.diagram[:,x] = [kw[v] for v in sub.diagram[x]]
  end
  return Schedule(sub, newer_x)
end 


# General Trajectory and Schedule datatypes 
###########################################

struct TrajStep 
  desc::String
  world::ACSetTransformation
  pmap::Span{<:StructACSet} # nothing == id
  inwire::Wire
  outwire::Wire
  function TrajStep(d,w,p,i,o)
    noattr(w) || error("World state has variables $w")
    codom(right(p)) == codom(w) || error("World doesn't match pmap")
    return new(d,w,p,i,o)
  end
end 

"""
Structure of a trajectory of a "world state" that is generated via traversal of 
a schedule. The data for each step in time is a world state (with a 
distinguished agent) as well as a wire ID that one is living on. Furthermore,
between the world states, there are partial maps to show how they are related 
to each other.
"""
mutable struct Traj
  initial::ACSetTransformation 
  steps::Vector{TrajStep}
  Traj(i::ACSetTransformation) = new(i, TrajStep[])
end 
Base.last(t::Traj) = last(t.steps)
Base.isempty(t::Traj) = isempty(t.steps)
Base.length(t::Traj) = length(t.steps)
Base.getindex(t::Traj, i::Int) = t.steps[i]
get_agent(t::Traj, i::Int) = i == 0 ? t.initial : t[i].world
traj_res(s::Traj) = codom(traj_agent(s))
traj_agent(t::Traj) = isempty(t.steps) ? t.initial : last(t).world
Base.push!(t::Traj, ts::TrajStep) = push!(t.steps, ts)

"""
Take a morphism (pointing at world state #i) and push forward to current time.
"""
function update_agent(t::Traj, i::Int, a::ACSetTransformation; check=false)
  !check || is_natural(a) || error("Updating unnatural a")
  noattr(a) || error("World state has variables")
  if i < 0
    error("Called update with negative index $i")
  elseif i == length(t) # special case
    codom(a) == codom(get_agent(t, i)) || error("BAD MATCH $i $a")
    return a
  end 
  codom(a) == codom(left(t[i+1].pmap)) || error("BAD MATCH $i $a")
  for j in i+1:length(t)
    a = postcompose_partial(t[j].pmap, a)
    if check && !is_natural(a) 
      println("dom(a)"); show(stdout, "text/plain", dom(a))
      println("codom(a)"); show(stdout, "text/plain", codom(a))
      error("Updated unnatural a $(collect(pairs(components(a))))")
    end
    if isnothing(a) return nothing end 
  end
  codom(a) == traj_res(t) || error("Failed to postcompose $(codom(a))\n$(traj_res(t))")
  return a 
end

"""
Type for primitive boxes used in a schedule. These are the generating morphisms
of a traced monoidal category, with objects being lists of ACSets.
"""
abstract type AgentBox end 
mk_box(a::AgentBox) = Box(a, input_ports(a), output_ports(a))
Base.show(io::IO, c::AgentBox) = show(io, string(c))
Base.string(c::AgentBox) = string(name(c))

input_ports(::AgentBox)::Vector{StructACSet} = error("Not yet defined")
output_ports(::AgentBox)::Vector{StructACSet} = error("Not yet defined")
initial_state(::AgentBox) = error("Not yet defined") 
color(::AgentBox) = error("Not yet defined") 
name(a::AgentBox) = a.name
(::Migrate)(::AgentBox) = error("Not yet defined")

""" In x P x S -> Out x P x S x Msg ---- output P actually just needs the maps
Xₙ₋₁ -/-> X and A -> X, which get concatenated to the input trajectory P
"""
update(::AgentBox, iid_wire::Int, instate::Traj) = error("Not yet defined") 

"""Make a wiring diagram around a box"""
function singleton(b::AgentBox)::Schedule
  ips, ops = input_ports(b), output_ports(b)
  wd = WD(ips, ops)
  add_box!(wd, mk_box(b))
  add_wires!(wd, [
    [Wire(ip,(input_id(wd),i),(1,i)) for (i, ip) in enumerate(ips)]...,
    [Wire(op,(1,i),(output_id(wd),i)) for (i, op) in enumerate(ops)]...,])
  iob, oob = otimes.([TM.Ob[Ob(TM, x) for x in xs] for xs in [ips,ops]])
  x = Hom(name(b), iob, oob)
  return Schedule(wd, x)
end


const WD = WiringDiagram{ThTracedMonoidalWithBidiagonals, StructACSet, 
                         StructACSet, AgentBox}

# It would be nice if ⊗ and ⋅ preserved the type of WDs, then we could more 
# strongly type our code.
struct Schedule 
  d::WD
  x::GATExpr
  Schedule(d,x) = new(typecheck(d), x)
end
struct SPorts p::Ports end 
input_ports(s::Schedule)::Vector{StructACSet} = input_ports(s.d)
output_ports(s::Schedule)::Vector{StructACSet} = output_ports(s.d)


@instance ThTracedMonoidalWithBidiagonals{SPorts, Schedule} begin
  @import dom, codom

  id(A::SPorts) =  Schedule(id(A.p), to_hom_expr(TM,id(A.p)))
  compose(f::Schedule, g::Schedule) = Schedule(f.d ⋅ g.d, f.x ⋅ g.x)
  otimes(A::SPorts, B::SPorts) = SPorts(A.p ⊗ B.p)
  munit(::Type{SPorts}) = SPorts(munit(Ports))
  otimes(f::Schedule, g::Schedule) = Schedule(f.d⊗g.d,f.x ⊗ g.x)
  braid(A::SPorts, B::SPorts) = SPorts(braid(A.p,B.p))
  trace(X::SPorts, A::SPorts, B::SPorts,f::Schedule) = 
    Schedule(trace(X,A.p,B.p,f.d), trace(X,A,B,f.x)) 
  mmerge(A::SPorts;i=2) = let m = mmerge(A.p,i); 
    Schedule(m, to_hom_expr(TM,m)) end
  create(A::SPorts) = mmerge(A;i=0)
end


# Automatically call singleton when composing boxes w/ wiring diagrams
compose(x::AgentBox, y::Union{Schedule, AgentBox}) = compose(singleton(x), y)
compose(x::Schedule, y::AgentBox) = compose(x, singleton(y))
⋅(x::AgentBox, y::Union{Schedule, AgentBox}) = ⋅(singleton(x), y)
⋅(x::Schedule, y::AgentBox) = ⋅(x, singleton(y))
otimes(x::AgentBox, y::Union{Schedule, AgentBox}) = otimes(singleton(x), y)
otimes(x::Schedule, y::AgentBox) = otimes(x, singleton(y))
⊗(x::AgentBox, y::Union{Schedule, AgentBox}) = ⊗(singleton(x), y)
⊗(x::Schedule, y::AgentBox) = ⊗(x, singleton(y))


# make the theory of mk_sched tracedmonoidalcategory 
# use Functor to do GATExpr substitution


"""Map a functor over the data of a schedule"""
function (F::Migrate)(wd_::Schedule) 
  wd = deepcopy(wd_.d)
  for x in [:value, Symbol.(["$(x)_port_type" for x in 
                            [:outer_in,:outer_out,:out,:in]])..., 
                    Symbol.(["$(x)wire_value" for x in ["",:in_,:out_]])...]
    wd.diagram[:,x] = F.(wd.diagram[x])
  end 
  return Schedule(wd,wd_.x)
end 

const wnames = [
  # Begin   End          Val            BeginType             EndType
  [:src,    :tgt,    :wire_value,    :out_port_type,      :in_port_type],
  [:in_src, :in_tgt, :in_wire_value, :outer_in_port_type, :in_port_type],
  [:out_src,:out_tgt,:out_wire_value,:out_port_type,      :outer_out_port_type]
]

typecheck(s::Schedule) = begin typecheck(s.d); return s end 

function typecheck(wd::WiringDiagram)::WD 
  wd = deepcopy(wd)
  for (i, (s,t,wval,sval,tval)) in enumerate(wnames)
    for (w,vs) in enumerate(wire_vals(wd, i))
      if length(vs) != 1 
        if i == 1
          error("#$wval $w $(wd.diagram[w,[:src, :out_port_box,:value]]) $(wd.diagram[w,[:tgt, :in_port_box,:value]]) $vs")
        else
          error("#$wval $w $vs") 
        end
      end 
      set_subpart!(wd.diagram, w,  wval, only(vs))
      set_subpart!(wd.diagram, wd.diagram[w,s], sval, only(vs))
      set_subpart!(wd.diagram, wd.diagram[w,t], tval, only(vs))
    end
  end
  wd2 = WD([],[])
  copy_parts!(wd2.diagram, wd.diagram)
  return wd2
end

"""1 = wire, 2 = inwire, 3 = outwire"""
function wire_vals(wd::WiringDiagram, i::Int)
  (s,t,wval,sval,tval) = wnames[i]
  map(enumerate(zip(wd.diagram[s], wd.diagram[t]))) do (i, (op, ip))
    d = [wd.diagram[i,wval], wd.diagram[op, sval],wd.diagram[ip, tval]]
    return unique(filter(x->!isnothing(x), collect(values(d))))
  end 
end



"""
The comonoid structure - merging multiple wires into one. This is unproblematic
because the world state only ever exists on one wire at a given time.
"""
merge_wires(agent::StructACSet, n::Int=2)::Schedule = 
  mmerge(SPorts(Ports([agent]));i=n)
id(agents::AbstractVector{<:StructACSet}) = id(SPorts(Ports(agents)))


end # module 