
"""
We can convert any petri net into a ABM, giving it the "token-passing"
semantics, by converting each transition into a rewrite rule.
"""

using AlgebraicPetri
using AlgebraicRewriting
using Catlab.Present, Catlab.Theories, Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.CSetDataStructures: struct_acset

sir_petri = LabelledPetriNet([:S,:I,:R],
                              :inf=>((:S,:I)=>(:I,:I)),
                              :rec=>(:I=>:R))

"""
The states of a Petri net induce a discrete schema for a C-Set
"""
function petri_to_cset_type(p::LabelledPetriNet, name::Symbol=:Discrete)::Type
  pres = Presentation(FreeSchema)
  [add_generator!(pres, Ob(FreeSchema, l)) for l in p[:sname]]
  expr = struct_acset(name, StructACSet, pres)
  eval(expr)
  return eval(name)
end

SIR = petri_to_cset_type(sir_petri)

"""
The rewrite rule matches for the inputs to the transition, deletes them, and
adds the outputs to the transition.
"""
function transition_to_rw_rule(p::LabelledPetriNet, t::Int)
  Rule(map([(:it,:is), (:ot,:os)]) do (getIO, getState)
    cset = petri_to_cset_type(p)()
    [add_part!(cset, x) for x in p[incident(p, 1, getIO), [getState,:sname]]]
    return create(cset) # interface I is an empty C-Set
  end...)
end

rw = transition_to_rw_rule(sir_petri, 1)
codom(rw.L) # C-Set with S=1 and I=1
codom(rw.R) # C-Set with I=2
