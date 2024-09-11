module RuleApps
export RuleApp, loop_rule, tryrule, succeed

using StructEquality

using Catlab.CategoricalAlgebra, Catlab.Theories

using ...Rewrite
using ...Rewrite.Utils: AbsRule, get_rmap, get_pmap, get_expr_binding_map
using ...Rewrite.Inplace: interp_program!
using ...CategoricalAlgebra.CSets: extend_morphism_constraints
using ..Wiring, ..Poly, ..Eval, ..Basic
using ..Wiring: str_hom, mk_sched
import ..Wiring: AgentBox, input_ports, output_ports, initial_state, color, update!
using ..Conditionals

import ACSets: sparsify


"""
Has the semantics of applying the rule to *some* match that is found 
(no guarantees on *which* one, which should be controlled by application 
conditions). If rewrite occurs, exit mode 1, else exit mode 2.

The agent is related to the L and R patterns of the rule. This can be done 
via a Span, or implicitly as a homomorphism into "I" of the rewrite 
rule, and alternatively just from the shape of the agent alone (if it is 
identical to I, take the id map, otherwise take the unique morphism into I).
"""
@struct_hash_equal struct RuleApp <: AgentBox
  name::Symbol 
  rule::AbsRule 
  in_agent::ACSetTransformation  # map A --> L 
  out_agent::ACSetTransformation # map A --> R
  prog::RewriteProgram
  """Give the data explicitly"""
  function RuleApp(n,r::AbsRule, i::ACSetTransformation, o::ACSetTransformation) 
    codom(i) == codom(left(r)) || error("Bad i for ruleapp $n")
    codom(o) == codom(right(r)) || error("Bad o for ruleapp $n")
    return new(n,r,i,o,compile_rewrite(r))
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
(F::SimpleMigration)(a::RuleApp) = 
  RuleApp(a.name,F(a.rule), F(a.in_agent), F(a.out_agent))
sparsify(a::RuleApp) = 
  RuleApp(a.name,sparsify(a.rule), sparsify(a.in_agent), sparsify(a.out_agent))

function update!(::Ref, r::RuleApp, g::ACSetTransformation, inport::Int)
  inport == 1 || error("Rule app has only one in port")
  m = update_match(r, g)
  if isnothing(m)
    return (g, 2, "No match")
  else
    rmap_components = interp_program!(r.prog, m.components, codom(g))
    rmap = ACSetTransformation(rmap_components, codom(r.rule.R), codom(g))
    return (compose(r.out_agent, rmap), 1, "Success")
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
