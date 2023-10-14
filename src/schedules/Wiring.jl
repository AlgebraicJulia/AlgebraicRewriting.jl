module Wiring
export Schedule, Names, mk_sched, typecheck, merge_wires, 
       singleton, traj_res, traj_agent

using Catlab, Catlab.CategoricalAlgebra, Catlab.WiringDiagrams, Catlab.Programs,
      Catlab.Theories
import Catlab.WiringDiagrams.DirectedWiringDiagrams: input_ports,output_ports
import Catlab.Theories: Ob,Hom,id, create, compose, otimes, ⋅, ⊗, ∇,□, trace, munit, braid, dom, codom, mmerge
using ..Theories: TM, ThTracedMonoidalWithBidiagonals
using ...CategoricalAlgebra.CSets
using ..Poly

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

struct Names{T}
  from_name::Dict{String,T}
  to_name::Dict{T,String}
  Names(d::Dict{String,T}) where T = new{T}(d, Dict([v=>k for (k,v) in collect(d)]))
end
Names(d::Dict) = Names(Dict([string(k)=>v for (k,v) in collect(d)]))
Names(;kw...) = Names(Dict([string(k)=>v for (k,v) in pairs(kw)]))
Base.getindex(n::Names,s::String) = n.from_name[s]
Base.getindex(n::Names,s::Symbol) = n[string(s)]
Base.getindex(n::Names,x)::String = get(n.to_name,x,"?")
Base.length(n::Names) = length(n.from_name)
function Base.setindex!(n::Names{T}, y::T, x::String) where T 
  n.from_name[x] = y 
  n.to_name[y] = x
end
(F::Migrate)(n::Names) = Names(F(n.from_name))

# General wiring diagram utilities
###################################

"""
Make a wiring diagram with ob/hom generators using @program macro

TODO double check that this does not introduce any wire splitting.
"""
function mk_sched(t_args::NamedTuple,args::NamedTuple,names::Names{T},
                  kw::Union{NamedTuple,AbstractDict}, wd::Expr) where T
  n_trace=length(t_args)
  os = Dict{Symbol, T}(Symbol(k)=>v for (k,v) in collect(names.from_name))
  hs = Dict{Symbol, Schedule}(Symbol(k)=>v isa AgentBox ? singleton(v) : v for (k,v) in pairs(kw))
  P = Presentation(TM)
  os_ = Dict(v=>add_generator!(P, Ob(TM,k)) for (k,v) in collect(os))

  for (k,v) in collect(pairs(hs))
    i = (isempty(input_ports(v)) 
        ? munit(TM.Ob) 
        : otimes([os_[ip] for ip in input_ports(v)]))
    o = (isempty(output_ports(v)) ? munit(TM.Ob) : otimes([os_[op] for op in output_ports(v)]))
    add_generator!(P, Hom(k, i, o))
  end
  args_ = Expr(:tuple,[Expr(Symbol("::"), k,v) for (k,v) in pairs(merge(t_args,args))]...)
  tmp = parse_wiring_diagram(P, args_, wd)
  Xports = Ports{ThTracedMonoidalWithBidiagonals}(input_ports(tmp)[1:n_trace])
  newer_x = Ob(TM,Xports) # arbitrary gatexpr
  try 
    tmpx = to_hom_expr(TM, tmp)
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

  catch e
    if !(e isa AssertionError && e.msg == "inputs == outputs[σ]")
      throw(e)
    end
  end 

  new_d = trace(Xports, tmp)
  sub = ocompose(new_d, WiringDiagram[hs[Symbol(b.value)].d for b in boxes(new_d)])
  sub.diagram[:wire_value] = nothing
  for x in Symbol.(["$(x)_port_type" for x in [:outer_in,:outer_out,]])
    sub.diagram[:,x] = [names[v] for v in sub.diagram[x]]
  end

  return Schedule(sub, newer_x)
end 



"""
Type for primitive boxes used in a schedule. These are the generating morphisms
of a traced monoidal category, with objects being lists of ACSets.
"""
abstract type AgentBox end 
mk_box(a::AgentBox) = Box(a, input_ports(a), output_ports(a))
Base.show(io::IO, c::AgentBox) = show(io, string(c))
Base.string(c::AgentBox) = string(name(c))
name(a::AgentBox) = a.name

input_ports(::AgentBox)::Vector{StructACSet} = error("Not yet defined")
output_ports(::AgentBox)::Vector{StructACSet} = error("Not yet defined")
initial_state(::AgentBox) = error("Not yet defined") 
color(::AgentBox) = error("Not yet defined") 
(::Migrate)(::AgentBox) = error("Not yet defined")
update(::AgentBox, p::PMonad) = error("Not yet defined")

"""Make a wiring diagram around a box"""
function singleton(b::AgentBox)::Schedule
  ips, ops = input_ports(b), output_ports(b)
  wd = WD(ips, ops)
  add_box!(wd, mk_box(b))
  add_wires!(wd, [
    [Wire(nothing,(input_id(wd),i),(1,i)) for (i, ip) in enumerate(ips)]...,
    [Wire(nothing,(1,i),(output_id(wd),i)) for (i, op) in enumerate(ops)]...,])
  iob, oob = otimes.([TM.Ob[Ob(TM, x) for x in xs] for xs in [ips,ops]])
  x = Hom(name(b), iob, oob)
  return Schedule(wd, x)
end


const WD = WiringDiagram{ThTracedMonoidalWithBidiagonals, StructACSet,
                         StructACSet, AgentBox}

# It would be nice if ⊗ and ⋅ preserved the type of WDs, then we could more
# strongly type our code.
struct Schedule 
  d::WiringDiagram{<:ThTracedMonoidalWithBidiagonals}
  x::GATExpr
  function Schedule(d,x) 
    wd = WiringDiagram{ThTracedMonoidalWithBidiagonals,Any,Any,Any}([],[])
    copy_parts!(wd.diagram, d.diagram)
    return new(wd, x)
  end
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

function typecheck(wd::WiringDiagram)
  wd = deepcopy(wd)
  for (i, (s,t,wval,sval,tval)) in enumerate(wnames)
    for (w,vs) in enumerate(wire_vals(wd, i))
      if length(vs) != 1  error("#$wval $w $vs") end 
      set_subpart!(wd.diagram, w,  wval, only(vs))
      set_subpart!(wd.diagram, wd.diagram[w,s], sval, only(vs))
      set_subpart!(wd.diagram, wd.diagram[w,t], tval, only(vs))
    end
  end
  return wd
end

"""1 = inwire, 2 = outwire"""
function wire_vals(wd::WiringDiagram, i::Int)
  (s,t,_,sval,tval) = wnames[i]
  map(zip(wd.diagram[s], wd.diagram[t])) do (op, ip)
    d = [wd.diagram[op, sval],wd.diagram[ip, tval]]
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
