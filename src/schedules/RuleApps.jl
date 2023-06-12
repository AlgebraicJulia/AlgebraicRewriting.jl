module RuleApps
export RuleApp, loop_rule, tryrule, succeed

using Catlab.CategoricalAlgebra, Catlab.Theories

using ...Rewrite
using ...Rewrite.Utils: AbsRule, get_rmap, get_pmap, get_expr_binding_map
using ...CategoricalAlgebra.CSets: Migrate, extend_morphism_constraints
using ..Wiring, ..Poly, ..Eval, ..Basic
using ..Wiring: str_hom, mk_sched
import ..Wiring: AgentBox, input_ports, output_ports, initial_state, color, update
using ..Conditionals
using ..Eval: Traj, traj_agent, id_pmap, add_step, nochange


"""
Has the semantics of applying the rule to *some* match that is found 
(no guarantees on *which* one, which should be controlled by application 
conditions). If rewrite occurs, exit mode 1, else exit mode 2.

The agent is related to the L and R patterns of the rule. This can be done 
via a Span, or implicitly as a homomorphism into "I" of the rewrite 
rule, and alternatively just from the shape of the agent alone (if it is 
identical to I, take the id map, otherwise take the unique morphism into I).
"""
struct RuleApp <: AgentBox
  name::Symbol 
  rule::AbsRule 
  in_agent::ACSetTransformation  # map A --> L 
  out_agent::ACSetTransformation # map A --> R
  """Give the data explicitly"""
  function RuleApp(n,r::AbsRule, i::ACSetTransformation, o::ACSetTransformation) 
    codom(i) == codom(left(r)) || error("Bad i for ruleapp $n")
    codom(o) == codom(right(r)) || error("Bad o for ruleapp $n")
    return new(n,r,i,o)
  end
  """Implicitly give data via a map A->I"""
  RuleApp(n,r::AbsRule, a::ACSetTransformation) = 
    RuleApp(n,r,a⋅left(r), a⋅right(r))
  """Implicitly give map A->I via just A"""
  function RuleApp(n,r::AbsRule, a::StructACSet)
    I = dom(left(r))
    h = (a == I) ? id(I) : only(homomorphisms(a, I))
    RuleApp(n, r, h)
  end
  """Empty agent by default"""
  RuleApp(n,r::AbsRule) = 
    RuleApp(n,r,create(dom(left(r))))
end  
input_ports(r::RuleApp) = [dom(r.in_agent)] 
output_ports(r::RuleApp) = [dom(r.out_agent), dom(r.in_agent)]
color(::RuleApp) = "lightblue"
initial_state(::RuleApp) = nothing 
(F::Migrate)(a::RuleApp) = 
  RuleApp(a.name,F(a.rule), F(a.in_agent), F(a.out_agent))

#

function update(r::RuleApp, p::PMonad=Maybe)#, ::Int, instate::Traj, ::Nothing)
  function update_ruleapp(::Nothing, w::WireVal; kw...)
    w.wire_id == 1 || error("RuleApps have exactly 1 input")
    last_step = traj_agent(w.val) # A -> X 
    m = update_match(r, last_step)
    if isnothing(m)
      return MealyRes(nothing, [(nothing,WireVal(2,nochange(w.val)))], "(no match)")
    else 
      res = rewrite_match_maps(r.rule, m)
      rmap = get_rmap(ruletype(r.rule), res)
      xmap = get_expr_binding_map(r.rule, m, res)
      new_agent = r.out_agent ⋅ rmap ⋅ xmap
      pl, pr = get_pmap(ruletype(r.rule), res)
      pmap = Span(pl, pr ⋅ xmap)
      msg = m isa ACSetTransformation ? str_hom(m) : str_hom(first(m)) # PBPO
      wv = WireVal(1,add_step(w.val,TrajStep(new_agent, pmap)))
      return MealyRes(nothing, [(nothing, wv)], msg)
    end
  end
end 


# """Helper function for `update`"""
function update_match(r::RuleApp, agent::ACSetTransformation; kwargs...)
  init = extend_morphism_constraints(agent, r.in_agent)
  get_match(r.rule, codom(agent); initial=init, kwargs...)
end 

"""
A box that takes the first output iff there is a match from a rule into the 
current state"""
has_match(rulename::String, r::AbsRule, agent::StructACSet) = 
  if_cond(Symbol("Can match $rulename"), x->!isnothing(get_match(r,x)), agent)

"""
Feed the "rewrite applied" output back into the input of the rule application
"""
function loop_rule(a::RuleApp)
  dom(a.in_agent) == dom(a.out_agent) || error("Cannot loop rule w/ different in/out agent")
  mk_sched((trace_arg=:X,), (i=:X,), Names(X=dom(a.in_agent)), (f=a,), 
            quote  f([i,trace_arg]) end) 
end
tryrule(a::RuleApp) = a ⋅ merge_wires(dom(a.in_agent))
succeed(a::RuleApp) = a ⋅ (id([dom(a.out_agent)]) ⊗ Fail(dom(a.in_agent)))

end # module 
