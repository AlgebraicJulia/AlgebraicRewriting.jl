module Callbacks
export CallbackBox

using Catlab, StructEquality

using ...CategoricalAlgebra.CSets: Migrate
using ..Poly
using ..Wiring: AgentBox
import ACSets: sparsify
import ..Wiring: input_ports, output_ports, initial_state, color, update!

@struct_hash_equal struct CallbackBox
  name::Symbol
  callback::Function
  agent::ACSet
  CallbackBox(n, c, a) = new(n, c, deepcopy(a))
end

input_ports(b::CallbackBox) = [b.agent]

output_ports(b::CallbackBox) = [b.agent]

initial_state(::CallbackBox) = nothing

color(b::CallbackBox) = "purple"

# Warning that the callback function cannot be functorially migrated
(F::Migrate)(b::CallbackBox) = CallbackBox(b.name, b.callback, F(b.agent))

sparsify(b::CallbackBox) = CallbackBox(b.name, b.callback, sparsify(b.agent))

function update!(::Ref, boxdata::CallbackBox, g::ACSetTransformation, ::Int)
  boxdata.callback(g)
  (g, 1, "")
end

end
