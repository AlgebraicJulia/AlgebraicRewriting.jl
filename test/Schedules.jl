module TestSchedules

using Test
using Catlab, Catlab.Theories, Catlab.WiringDiagrams, Catlab.Graphics
using Catlab.Graphs, Catlab.CategoricalAlgebra
using AlgebraicRewriting
using Interact
using Blink: Window, body!
function viewer(s,r)
  w = Window()
  body!(w, view_traj(s, r, to_graphviz))
end


# Simple workflow with control and rewriting 
############################################

z, g1, ar, loop = Graph(), Graph(1), path_graph(Graph, 2), apex(terminal(Graph))

av = RuleApp("add vertex", Rule(id(z), create(Graph(1)))) 
g2 = homomorphism(Graph(2), ar; monic=true)
de = loop_rule(RuleApp("del edge", Rule(g2, id(Graph(2)))))
coin = uniform(2, z)
merge2 = merge_wires(2,g1)

sched = (coin ⋅ (av ⊗ id_wires(1,z)) ⋅ merge2 ⋅ de)

G = path_graph(Graph, 4)
res = apply_schedule(sched, G);
# viewer(sched, res)

# Query workflow (add loop to each vertex)
##########################################
al = RuleApp("add loop", Rule(id(g1), homomorphism(g1,loop)), g1)
q = Query("Vertex", g1)

sched = mk_sched((i=:Z, o=:O), 1, Dict(:rule=>al, :query=>q, :Z=>z,:O=>g1), 
quote 
  q1,q2,q3 = query(i,o)
  trace = rule(q2)
  out = [q1,q3]
  return out, trace
end);

res = apply_schedule(sched, Graph(3))
# viewer(sched, res)


# Dependent query workflow 
# (flip to add loop to each vertex downstream of tgt, then add edge out of src)
##############################################################################
s_hom, t_hom = [ACSetTransformation(g1,ar; V=[i]) for i in 1:2]

q2 = Query(Span(t_hom,s_hom), "Out edges", g1)
ws = Weaken("Switch to src", s_hom)
wt = Weaken("Switch to tgt", t_hom)
str = Strengthen("Add outedge", s_hom)
maybe_add_loop = uniform(2, g1) ⋅ (al ⊗ id_wires(1,g1))

# graphviz(uniform(2, g1) ⋅ (al ⊗ id_wires(1,g1)) ⋅ merge_wires(2, g1); orientation=LeftToRight)


sched = mk_sched((init=:A, trace_arg=:V,), 1, Dict(
  :loop => maybe_add_loop, :out_edges=>q2, :weaken_src=>ws, 
  :weaken_tgt=>wt, :add=>str, :A=>ar,:V=>g1, :Z=>z), 
quote 
  added_loops, out_edge, ignore = out_edges(init, trace_arg)
  out_neighbor = weaken_tgt(out_edge)
  trace1, trace2 = loop(out_neighbor)
  out = add(weaken_src(added_loops))
  return out, [trace1, trace2]
end);


# graphviz(sched ⋅ sched; orientation=LeftToRight)

G = @acset Graph begin V=5; E=4; src=[1,2,2,5];tgt=[2,3,4,2] end 
arr_start = homomorphism(ar, G; initial=(V=[1,2],))
res = apply_schedule(sched, arr_start);
# viewer(sched, res)


# For-loop: add 3 loops
#######################
sched = for_schedule(maybe_add_loop ⋅ merge2, 3)
res = apply_schedule(sched, id(g1));
# viewer(sched, res)

end # module
