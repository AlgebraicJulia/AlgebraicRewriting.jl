module Queries 
export Query, agent

using Catlab, Catlab.CategoricalAlgebra, Catlab.WiringDiagrams

using ...Rewrite
using ...CategoricalAlgebra.CSets: Migrate
using ..Wiring
using ..Wiring: AgentBox, update_agent, id_pmap, str_hom, get_agent
import ..Wiring: input_ports, output_ports, initial_state, color, update
  


"""
Has an A input/output and a B input/output (by default, the B input can be 
changed to some other type if needed). 

    A  R ---------↖
    ↓  ↓          []  
  ⌜-------⌝       []
  | Query | [agent subroutine] 
  ⌞-------⌟       []
   ↓  ↓  ↓        []
   A  B  ∅        []
      ↘-----------↗
Performs one action per element of Hom(B,X), optionally with some constraints.
(i.e. sends you out along the B wire with agent Bₙ->X). 

After you have done this for all Bₙ, then you exit the A port (you need to 
update the A->X map, and, if at any point the agent was deleted, then you exit a 
third door typed by 0).

A constraint optionally will be applied to (1) the A->W<-B cospan of old agent 
and purported new agent. (the new agent is the first argument to the constraint) 

"""
struct Query <: AgentBox
  name::String
  agent::StructACSet
  subagent::StructACSet
  return_type::StructACSet
  constraint::Constraint
  Query(n::String,sa::StructACSet,a::Union{Nothing,StructACSet}=nothing, 
        ret::Union{StructACSet,Nothing}=nothing; constraint=Trivial) = 
    new(n, isnothing(a) ? typeof(sa)() : a, sa, 
        isnothing(ret) ? sa : ret, constraint)
  Query(sa::StructACSet,a::StructACSet=nothing, n::String="",ret=nothing; constraint=Trivial) = 
    Query(n,sa,a,ret;constraint=constraint)
  """ 
  Span Aₒ<-•->Aₙ relates old agent shape to new agent shape, such that the 
  new agent Aₙ->X makes the square commute. If constraint is nontrivial, this 
  constraint is added to it.

       rgt₂
      I₁-> B₃
  lft₁↓    ↓ λ₁
      A₂-> W₄
        λ₂
  """
  function Query(a::Span, n::String="", ret=nothing; constraint=Trivial)
    in_shape, agent_shape = codom.([left(a),right(a)])
    if arity(constraint) == 0 # trivial
      cg = @acset CGraph begin V=4; E=4; Elabel=1; src=[1,1,2,3]; tgt=[2,3,4,4]
        vlabel=[apex(a), in_shape, agent_shape, nothing]
        elabel=[a...,AttrVar.([2,1])...]
      end
      xpr = Commutes([1,3],[2,4])
    elseif arity(constraint) == 1 
      cg = deepcopy(constraint.g)
      v_a,v_l = add_vertices!(cg; vlabel=[apex(a),in_shape]) 
      e_r = findfirst(==(AttrVar(1)), cg[:elabel])
      v_r, v_w = [cg[e_r, x] for x in [:src,:tgt]]
      e1,e2,e3 = add_edges!(cg,[v_a,v_a,v_l],[v_l,v_r,v_w]; 
                 elabel=[a...,AttrVar(2)])
      xpr = BoolAnd(Commute([e1,e2],[e3,e_r]), constraint.d)
    else
      error("Odd constraint") 
    end 
    rshape = isnothing(ret) ? agent_shape : ret
    new(n, in_shape, agent_shape, rshape, Constraint(cg, xpr))
  end
  """
  Constrain agents with a map OldAgent -> NewAgent (triangle must commute)
  There is a generalization to make with the below function and the above 
  function, regarding the "extending" of a constraint.
        a
     A₁-> B₂ 
      λ₁↘ ↓ λ₂
         W₃
  """
  function Query(a::ACSetTransformation, n::String="", ret=nothing; constraint=Trivial)
    in_shape, agent_shape = [dom(a),codom(a)]

    if arity(constraint) == 0 # trivial
      cg = @acset CGraph begin V=3; E=3; Elabel=1; src=[1,2,1]; tgt=[2,3,3]
        vlabel=[in_shape, agent_shape, nothing]
        elabel=[a,AttrVar.([2,1])...]
      end
      xpr = Commutes([3],[1,2])
    elseif arity(constraint) == 1 
      cg = deepcopy(constraint.g)
      agent_new_vertex = add_vertex!(cg; vlabel=in_shape)
      input_edge = findfirst(==(AttrVar(1)), cg[:elabel])
      input_edge_src, input_edge_tgt = [cg[input_edge, x] for x in [:src,:tgt]]
      e1,e2 = add_edges!(cg,[agent_new_vertex,agent_new_vertex],
                            [input_edge_src,input_edge_tgt];
                             elabel=[a,AttrVar(2)])
      xpr = BoolAnd(Commutes([e2],[e1,input_edge]), constraint.d)
    else
      error("Odd constraint of arity $(arity(constraint))")
    end 
    rshape = isnothing(ret) ? agent_shape : ret
    new(n, in_shape, agent_shape, rshape, Constraint(cg, xpr))
  end
end

"""
Data structure maintaining the state of a Query primitive box.
We need to know when we first entered the box as well as the remaining homs 
that need to be processed.
"""
mutable struct QueryState 
  enter_time::Int 
  homs::Vector{ACSetTransformation}
end
Base.isempty(q::QueryState) = isempty(q.homs)
Base.pop!(q::QueryState) = deepcopy(pop!(q.homs))
Base.length(q::QueryState) = length(q.homs)
Base.string(c::Query) = "Query $(c.name)"
color(::Query) = "yellow"
input_ports(c::Query) = [c.agent, c.return_type] 
output_ports(c::Query) = [c.agent, c.subagent, typeof(c.agent)()]
initial_state(::Query) = QueryState(-1, ACSetTransformation[])
(F::Migrate)(a::Query) =  Query(a.name,F(a.agent), F(a.return_type))

function update(q::Query, i::Int, instate::Traj, boxstate::Any)
  idp = id_pmap(traj_res(instate))
  msg = ""
  curr_boxstate = (i != 1) ? boxstate : begin 
    ms = filter(h->apply_constraint(q.constraint, h, traj_agent(instate)),
                homomorphisms(q.subagent, traj_res(instate)))
    msg *= "Found $(length(ms)) agents"
    QueryState(length(instate), ms)
  end 

  if isempty(curr_boxstate) # END
    old_agent = get_agent(instate,curr_boxstate.enter_time)
    new_agent = update_agent(instate, curr_boxstate.enter_time, old_agent)
    if isnothing(new_agent) # original agent gone
      msg *= "\nCannot recover original agent."
      curr_boxstate.enter_time = -1
      return (3, create(traj_res(instate)), idp, curr_boxstate,msg)
    else # original agent recovered
      msg *= "\nExiting with original agent."
      curr_boxstate.enter_time = -1
      return (1, new_agent, idp, curr_boxstate,msg)
    end 
  else # CONTINUE 
    new_agent = update_agent(instate, curr_boxstate.enter_time, pop!(curr_boxstate))
    if isnothing(new_agent)
      println("Queued agent no longer exists")
      return update(q, i, instate, curr_boxstate)
    end
    msg *= "\nContinuing ($(length(curr_boxstate)) queued) with \n" * str_hom(new_agent)
    return (2, new_agent, idp, curr_boxstate,msg)
  end 
end


const ATypes = Union{Span,ACSetTransformation,Pair{StructACSet,StructACSet},
                     StructACSet}
function agent(s::WiringDiagram, sa::ATypes; n="agent", ret=nothing, 
               constraint=Trivial)
  if sa isa ACSetTransformation || sa isa Span 
    q = Query(sa, n, ret; constraint=constraint)
  elseif sa isa Pair{StructACSet,StructACSet}
    q = Query(n, sa[1], sa[2], ret; constraint=constraint)
  else 
    q = Query(n, sa, nothing, ret; constraint=constraint)
  end 
  a,b,z = output_ports(q)
  a_, c = input_ports(q)
  a == a_ || error("Bad ports")
  mk_sched((init=:A, trace_arg=:C,), 1, (
    query = q, sched=s, A=a, B=b, C=c, Z=z), quote 
      out, loop, _ = query(init, trace_arg)
      return out, sched(loop)
  end)
end 

end # module 