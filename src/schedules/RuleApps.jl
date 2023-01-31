module RuleApps
export RuleApp, loop_rule

using Catlab.CategoricalAlgebra

using ...Rewrite
using ...Rewrite.Utils: AbsRule, get_rmap, get_pmap, get_expr_binding_map
using ...CategoricalAlgebra.CSets: Migrate, extend_morphism_constraints
using ..Wiring
using ..Wiring: id_pmap, str_hom, traj_agent
import ..Wiring: AgentBox, input_ports, output_ports, initial_state, color, 
  update
using ..Conditionals


"""
Has the semantics of applying the rule to *some* match that is found 
(no guarantees on *which* one, which should be controlled by application 
conditions).

The agent is related to the L and R patterns of the rule. This can be done 
via a Span, or implicitly as a homomorphism into "I" of the rewrite 
rule, and alternatively just from the shape of the agent alone (if it is 
identical to I, take the id map, otherwise take the unique morphism into I).
"""
struct RuleApp <: AgentBox
  name::String 
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
Base.string(c::RuleApp) = c.name
input_ports(r::RuleApp) = [dom(r.in_agent)] 
output_ports(r::RuleApp) = [dom(r.out_agent)]
color(::RuleApp) = "lightblue"
initial_state(::RuleApp) = nothing 
(F::Migrate)(a::RuleApp) = 
  RuleApp(a.name,F(a.rule), F(a.in_agent), F(a.out_agent))


function update(r::RuleApp, ::Int, instate::Traj, ::Nothing)
  last_step = traj_agent(instate) # A -> X 
  ms = update_matches(r,last_step)
  if isempty(ms)
    return (1, last_step, id_pmap(codom(last_step)), nothing, "(no match)")
  else 
    m = first(ms)
    res = rewrite_match_maps(r.rule, m; check=true)
    rmap = get_rmap(ruletype(r.rule), res)
    xmap = get_expr_binding_map(r.rule, m, res)
    new_agent = r.out_agent ⋅ rmap ⋅ xmap
    pl, pr = get_pmap(ruletype(r.rule), res)
    pmap = Span(pl, pr ⋅ xmap)
    msg = m isa ACSetTransformation ? str_hom(m) : str_hom(first(m)) # PBPO
    return (1, new_agent, pmap, nothing, msg)
  end
end 
"""Helper function for `update` and `loop_rule`"""
function update_matches(r::RuleApp, agent::ACSetTransformation; kwargs...)
  init = extend_morphism_constraints(agent, r.in_agent)
  get_matches(r.rule, codom(agent); initial=init, kwargs...)
end 

"""
A box that takes the first output iff there is a match from a rule into the 
current state"""
has_match(rulename::String, r::AbsRule, agent::StructACSet) = 
  if_cond("Can match $rulename", x->!isempty(get_matches(r,x)), agent)


loop_rule(a::RuleApp) =
  while_schedule(a, x->!isempty(update_matches(a,x)); 
                 name = "match $(a.name)", argtype = :agent)


end # module 