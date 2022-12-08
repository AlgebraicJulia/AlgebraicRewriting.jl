module TestSchedules
using Test
using Catlab, Catlab.Theories, Catlab.WiringDiagrams, Catlab.Graphics, Catlab.Programs
using Interact
using AlgebraicRewriting
using Blink: Window, body!

using Catlab.Graphs

av = RuleSchedule("add vertex",
  Rule(id(Graph()), create(Graph(1))))
de = RuleSchedule("del edge",
  Rule(homomorphism(Graph(2), path_graph(Graph, 2); monic=true), id(Graph(2)));
  loop=true)
coin = NestedDWD(uniform(2))
sched = (coin ⋅ (av ⊗ id(NPorts(1))) ⋅ merge_wires(2) ⋅ de) |> ocompose |> outer 

G = path_graph(Graph, 4)
res = apply_schedule(sched,G);

w = Window()
body!(w, view_traj(sched, res, to_graphviz))

end # module
