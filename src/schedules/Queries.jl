module Queries 
export Query, agent

using Catlab, Catlab.CategoricalAlgebra, Catlab.WiringDiagrams

using ...Rewrite
using ...CategoricalAlgebra.CSets: Migrate
using ..Basic: Fail
using ..Wiring, ..Poly, ..Eval
using ..Wiring: AgentBox,  str_hom
import ..Wiring: input_ports, output_ports, initial_state, color, update
import ..Eval: Traj, update_agent, id_pmap, get_agent, traj_res, traj_agent, add_step



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
  name::Symbol
  agent::StructACSet
  subagent::StructACSet
  return_type::StructACSet
  constraint::Constraint
  Query(n::Symbol,sa::StructACSet,a::Union{Nothing,StructACSet}=nothing, 
        ret::Union{StructACSet,Nothing}=nothing; constraint=Trivial) = 
    new(n, isnothing(a) ? typeof(sa)() : a, sa, 
        isnothing(ret) ? sa : ret, constraint)
  Query(sa::StructACSet,a::StructACSet=nothing, n::Symbol=:Query,ret=nothing; constraint=Trivial) = 
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
  function Query(a::Span, n::Symbol=:Query, ret=nothing; constraint=Trivial)
    in_shape, agent_shape = codom.([left(a),right(a)])
    cg = @acset CGraph begin V=4; E=4; Elabel=1; src=[1,1,2,3]; tgt=[2,3,4,4]
      vlabel=[apex(a), in_shape, agent_shape, nothing]
      elabel=[a...,2,1]
    end
    constr = Constraint(cg, Commutes([1,3],[2,4])) ⊗ constraint
    rshape = isnothing(ret) ? agent_shape : ret
    new(n, in_shape, agent_shape, rshape, constr)
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
  function Query(a::ACSetTransformation, n::Symbol=:Query, ret=nothing; constraint=Trivial)
    in_shape, agent_shape = [dom(a),codom(a)]
    cg = @acset CGraph begin V=3; E=3; src=[1,2,1]; tgt=[2,3,3]
      vlabel=[in_shape, agent_shape, nothing]
      elabel=[a,2,1]
    end
    constr = Constraint(cg, Commutes([3],[1,2])) ⊗ constraint
    rshape = isnothing(ret) ? agent_shape : ret
    new(n, in_shape, agent_shape, rshape, constr)
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
(F::Migrate)(a::Query) =  Query(F(a.subagent), F(a.agent), a.name, 
                                F(a.return_type); constraint=F(a.constraint))

#

function update(q::Query, p::PMonad=Maybe)#instate::Traj, ::Nothing)
  function update_query(S,w::WireVal; kw...)
    idp = id_pmap(traj_res(w.val)) 
    msg = ""
    curr_boxstate = (w.wire_id != 1) ? S : begin 
      ms = filter(h->apply_constraint(q.constraint, h, traj_agent(w.val)),
                  homomorphisms(q.subagent, traj_res(w.val)))
      msg *= "Found $(length(ms)) agents"
      @info "Found $(length(ms)) agents"
      QueryState(length(w.val), ms)
    end 
  
    if isempty(curr_boxstate) # END
      @info "No more subagents"
      old_agent = get_agent(w.val,curr_boxstate.enter_time)
      new_agent = update_agent(w.val, curr_boxstate.enter_time, old_agent)
      if isnothing(new_agent) # original agent gone
        msg *= "\nCannot recover original agent."
        curr_boxstate.enter_time = -1
        wv = WireVal(3, add_step(w.val, TrajStep(create(traj_res(w.val)), idp)))
        return MealyRes(curr_boxstate, [(nothing,wv)], msg)
      else # original agent recovered
        msg *= "\nExiting with original agent."
        curr_boxstate.enter_time = -1
        wv = WireVal(1,add_step(w.val, TrajStep(new_agent, idp)))
        return MealyRes(curr_boxstate,[(nothing,wv)], msg)
      end 
    else # CONTINUE 
      @info "Updating agents"
      new_agent = update_agent(w.val, curr_boxstate.enter_time, pop!(curr_boxstate))
      if isnothing(new_agent)
        @info "WARNING: Queued agent no longer exists"
        return update_query(curr_boxstate, w; kw...)
      end
      msg *= "\nContinuing ($(length(curr_boxstate)) queued) with \n" * str_hom(new_agent)
      wv = WireVal(2, add_step(w.val, TrajStep(new_agent, idp)))
      return MealyRes(curr_boxstate, [(nothing, wv)] ,msg)
    end 
  end
end


const ATypes = Union{Span,ACSetTransformation,StructACSet,Nothing}
function agent(s::Schedule, in_agent::ATypes=nothing;
               n=:agent, ret=nothing, constraint=Trivial)
  subagent = only(input_ports(s))
  outagent = only(output_ports(s)) 
  e = "agent() requires [A]->[A] wiring diagram"
  (isnothing(ret) && outagent == subagent) || outagent == ret || error(e)

  if in_agent isa ACSetTransformation || in_agent isa Span
    in_agent isa Span || dom(in_agent) == subagent || error("Bad span input")
    in_agent isa ACSetTransformation || codom(left(in_agent)) == subagent || error("Bad hom input")
    q = Query(in_agent, n, ret; constraint=constraint)
  elseif in_agent isa StructACSet || isnothing(in_agent)
    q = Query(n, subagent, in_agent, ret; constraint=constraint)
  else 
    error("in_agent of type $(typeof(in_agent))")
  end 
  a,b,z = output_ports(q)
  a_, c = input_ports(q)
  a == a_ || error("Bad ports")
  init_sym = (a == c) ? (:C) : (:A)
  mk_sched((trace_arg=:C,), (init=init_sym,), Names(A=a, B=b, C=c, Z=z), (
    query = q, sched=s, fail=Fail(typeof(a)())), quote 
      out, loop, ignore = query(init, trace_arg)
      fail(ignore)
      return sched(loop), out
  end)
end 

end # module
