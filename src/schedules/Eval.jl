module Eval 
export apply_schedule, rewrite_schedule

using Catlab.CategoricalAlgebra, Catlab.WiringDiagrams

using ..Wiring
using ..Wiring: initial_state, update


# Executing schedules 
#####################

"""
Execute a single primitive box (either a Conditional or a NamedRule).
Return output wire.
"""
function apply_schedule_step(s::Schedule, P::Traj, S::AbstractVector, 
                             iw::Wire; verbose=verbose)::Wire 
  I = iw.target # in port
  box = boxes(s)[I.box]
  if verbose println("Box $(box.value) port $(I.port)") end
  O, dP₁, dP₂, S′, msg = update(box.value, I.port, P, S[I.box])
  S[I.box] = S′ # update the box state 
  ow = only(out_wires(s, Port(I.box,OutputPort,O))) # no branching allowed!
  msg = "$(box.value.name)\n$msg"
  if verbose println(msg) end 
  push!(P, TrajStep(msg, dP₁, dP₂, iw, ow))
  return ow
end

"""Execute an entire schedule. Optionally limit # of steps"""
function apply_schedule(s_::WiringDiagram,g::ACSetTransformation; in_port=1,
                        steps::Int=-1, verbose::Bool=false)::Traj
  # Validate
  s = typecheck(s_)
  input_ports(s)[in_port] == dom(g) || error("Bad input agent to schedule")
  # Initialize
  P = Traj(g)
  boxstates = [initial_state(b) for b in s.diagram[:value]]
  curr_wire = only(out_wires(s, Port(input_id(s),OutputPort,in_port)))
  # Loop
  while (steps != 0) && (curr_wire.target.box != output_id(s))
    if verbose println("STEP $(length(P)+1) ($steps)") end
    steps -= 1
    curr_wire = apply_schedule_step(s, P, boxstates, curr_wire; verbose=verbose)
  end 
  return P
end

# assuming input has 0 agent.
apply_schedule(s::WiringDiagram,g::StructACSet; kw...) = 
  apply_schedule(s, create(g); kw...)

"""Just get the result from applying the schedule"""
rewrite_schedule(s::WiringDiagram, G; kw...) = 
  traj_res(apply_schedule(s, G; kw...))



end # module 
