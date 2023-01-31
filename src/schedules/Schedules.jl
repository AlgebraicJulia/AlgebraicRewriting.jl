module Schedules
export Schedule, Traj, id_wire, id_wires, mk_sched, traj_res, typecheck,
       Query, RuleApp, Weaken, Strengthen, Conditional, Initialize,
       loop_rule, const_cond, if_cond, has_match,
       uniform, merge_wires, while_schedule, for_schedule, agent, singleton,
       rewrite_schedule, apply_schedule, migrate_schedule, graphviz,
       input_ports, output_ports
       

using DataStructures, Random



# using ..CategoricalAlgebra.CSets: 
#   postcompose_partial, extend_morphism_constraints, extend_morphisms, Migrate,
#   abstract

using Reexport

include("Wiring.jl")
include("Basic.jl")
include("Conditionals.jl")
include("RuleApps.jl")
include("Queries.jl")
include("Eval.jl")
include("Visuals.jl")


@reexport using .Wiring
@reexport using .Basic
@reexport using .Conditionals
@reexport using .RuleApps
@reexport using .Queries
@reexport using .Eval
@reexport using .Visuals

end # module
