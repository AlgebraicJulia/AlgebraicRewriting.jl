module TestEval

using Test

using Catlab, AlgebraicRewriting
using Catlab.Graphics: to_graphviz_property_graph

using Luxor
using PrettyTables


# Graph + agent viewer 
######################
@acset_type Grph(SchGraph, part_type=BitSetParts, index=[:src,:tgt]) <: AbstractGraph

view_graph(a::Grph, path=tempname()) = view_graph(create(a), path)

function view_graph(a::ACSetTransformation{Grph}, path=tempname())
  g = codom(a)
  pg = to_graphviz_property_graph(g)
  for v in collect(a[:V])
    set_vprops!(pg, v, Dict([:style=>"filled",:color=>"red",:fillcolor=>"red"]))
  end
  for e in collect(a[:E])
    set_eprops!(pg, e, Dict([:color=>"red"]))
  end
  gv = to_graphviz(pg)
  open(path, "w") do io
    show(io,"image/svg+xml",gv)
  end
  return gv
end

# Simple workflow with control and rewriting 
############################################

(z, g1, g2), ar, loop = Grph.(0:2), path_graph(Grph, 2), apex(terminal(Grph))

N=Names(Dict("Z"=>z,"•"=>g1))
@test length(N) == 2
N["•→•"] = ar
Dot, A = Symbol.([N[g1],N[ar]]) 

av = RuleApp(:add_vertex, Rule(id(z), create(g1)))
g2ar = homomorphism(g2, ar; initial=(V=1:2,))
de = loop_rule(RuleApp(:del_edge, Rule(g2ar, id(g2))))
coin = uniform(2, z)
sched = coin ⋅ (tryrule(av) ⊗ id([z])) ⋅ merge_wires(z) ⋅ de

view_sched(sched, name="Simple schedule", names=N)
G = path_graph(Grph, 2)

@test interpret!(sched, G) isa ACSetTransformation
@test ne(G) == 0

res = interpret(sched, path_graph(Grph, 2))
view_traj(sched, res, view_graph; agent=true, names=N)

# Query workflow (add loop to each vertex)
##########################################
al = succeed(RuleApp(:add_loop, Rule(id(g1), homomorphism(g1,loop)), g1));
q = Query(:Vertex, g1)

bad_sched = mk_sched((trace_arg=Dot,), (i=:Z,), N, (rule=al, query=q), quote 
    q1,q2,q3 = query(i,trace_arg)
    trace = rule([q1,q2])
    out = [q3]
    return trace, out
end);

@test_throws ErrorException typecheck(bad_sched)



sched = mk_sched((o=Dot,), (i=:Z,), N, Dict(:rule=>al, :query=>q), 
  quote 
    q1,q2,q3 = query(i,o)
    trace = rule(q2)
    out = [q1,q3]
    return trace, out
  end
);

typecheck(sched)

view_sched(sched; names=N)
res = interpret(sched, Grph(3));
view_traj(sched, res, view_graph; agent=true, names=N)


# Dependent query workflow 
# (flip to add loop to each vertex downstream of tgt, then add edge out of src)
##############################################################################
s_hom, t_hom = [ACSetTransformation(g1, ar; V=[i]) for i in 1:2]

q2 = Query(Span(t_hom,s_hom), :OutEdges, g1)
ws = Weaken(:Switch_to_src, s_hom)
wt = Weaken(:Switch_to_tgt, t_hom)
str = Strengthen(:Add_outedge, s_hom)
maybe_add_loop = uniform(2, g1) ⋅ (al ⊗ id([g1]))

sched = mk_sched((trace_arg=Dot,), (init=A,), N, Dict(
  :loop => maybe_add_loop, :out_edges=>q2, :weaken_src=>ws, 
  :weaken_tgt=>wt, :add=>str, :fail=>Fail(z)), 
quote 
  added_loops, out_edge, ignore = out_edges(init, trace_arg)
  fail(ignore)
  out_neighbor = weaken_tgt(out_edge)
  trace1, trace2 = loop(out_neighbor)
  out = add(weaken_src(added_loops))
  return [trace1, trace2], out
end);

view_sched(sched; names=N)

G = @acset Grph begin V=5; E=4; src=[1,2,2,5];tgt=[2,3,4,2] end
arr_start = homomorphism(ar, G; initial=(V=[1,2],))
res = interpret(sched, arr_start);
view_traj(sched, res, view_graph; agent=true, names=N)
@test interpret!(sched, arr_start) isa ACSetTransformation

# For-loop: add 3 loops
#######################
sched = for_schedule(maybe_add_loop ⋅ merge_wires(g1), 3);
view_sched(sched)
interpret!(sched, id(g1)) |> codom

# TODO add an attributed example

end # module
