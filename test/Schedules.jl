module TestSchedules

using Test
using Catlab, Catlab.Theories, Catlab.WiringDiagrams, Catlab.Graphics
using Catlab.Graphs, Catlab.CategoricalAlgebra
using Catlab.Graphics: to_graphviz_property_graph

using AlgebraicRewriting

using Luxor

# Graph + agent viewer 
######################
function view_graph(a)
  g = codom(a)
  pg = to_graphviz_property_graph(g)
  for v in collect(a[:V])
    set_vprops!(pg, v, Dict([ :style=>"filled",:fillcolor=>"red"]))
  end
  for e in collect(a[:E])
    set_eprops!(pg, e, Dict([:color=>"red"]))
  end
  return to_graphviz(pg)
end
# Simple workflow with control and rewriting 
############################################

z, g1, ar, loop = Graph(), Graph(1), path_graph(Graph, 2), apex(terminal(Graph))

av = RuleApp("add vertex", Rule(id(z), create(Graph(1))))
g2 = homomorphism(Graph(2), ar; monic=true)
de = loop_rule(RuleApp("del edge", Rule(g2, id(Graph(2)))))
coin = uniform(2, z)
merge2 = merge_wires(2,g1)

sched = (coin ⋅ (tryrule(av) ⊗ id_wires(1,z)) ⋅ merge2 ⋅ de)

G = path_graph(Graph, 4)
res = apply_schedule(sched, G);
view_traj(sched, res, view_graph; agent=true)

# Query workflow (add loop to each vertex)
##########################################
al = tryrule(RuleApp("add loop", Rule(id(g1), homomorphism(g1,loop)), g1))
q = Query("Vertex", g1)

sched = mk_sched((i=:Z, o=:O), 1, Dict(:rule=>al, :query=>q, :Z=>z,:O=>g1), 
quote 
  q1,q2,q3 = query(i,o)
  trace = rule(q2)
  out = [q1,q3]
  return out, trace
end);

res = apply_schedule(sched, Graph(3))
view_traj(sched, res, view_graph; agent=true)


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
view_traj(sched, res, view_graph; agent=true)
view_traj(sched, res, to_graphviz; agent=false)


# For-loop: add 3 loops
#######################
sched = for_schedule(maybe_add_loop ⋅ merge2, 3)
res = apply_schedule(sched, id(g1));


# Simple game of life 
#####################
@present SchLifeGraph <: SchGraph begin # inherit Graph schema
  Cell::Ob
  (Life, Eng)::AttrType
  (cell_W,cell_E,cell_S,cell_N)::Hom(Cell, E)
  live::Attr(Cell, Life)
  eng::Attr(Cell, Eng)
end
@acset_type AbsLifeGraph(SchLifeGraph)
const LG = AbsLifeGraph{Bool,Int}

# A generic cell
Cell = @acset LG begin Cell=1; V=4; E=4; Life=1; Eng=1
  src=[1,1,2,3]; tgt=[2,3,4,4]; live=[AttrVar(1)]; eng=[AttrVar(1)] 
  cell_S=1; cell_W=2; cell_E=3; cell_N=4
end 

# Rule which updates eastern neighbor of a live cell to have +1 eng
inc_E_ = @acset LG begin Cell=2; V=6; E=7; Life=1; Eng=2
  src=[1,1,2,2,3,4,5]; tgt=[2,4,3,5,6,5,6]; 
  cell_W=[2,4]; cell_E=[4,5]; cell_S=[1,3]; cell_N=[6,7]
  live=[true,AttrVar(1)]; eng=AttrVar.(1:2)
end
inc_E = Rule(id(inc_E_),id(inc_E_); expr=(Eng=[es->es[1],es->es[2]+1],))
inc_E_rule = RuleApp("incE",inc_E,homomorphism(Cell,inc_E_)) |> tryrule

# Assemble a schedule 
sched = agent(inc_E_rule, Cell, ret=Cell)


# Demonstrate on a 2 x 2 grid: 
# L D
# L D
G = @acset LG begin Cell=4; V=9; E=12
  src=[1,1,2,2,3,4,4,5,5,6,7,8]; tgt=[2,4,3,5,6,5,7,6,8,9,8,9]; 
  cell_W=[2,4,7,9]; cell_E=[4,5,9,10]; cell_S=[1,3,6,8]; cell_N=[6,8,11,12]
  live=[true,false,true,false]; eng=[1,10,100,1000]
end

res = apply_schedule(sched, G)

expected = deepcopy(G)
expected[:eng] = [1,11,100,1001] # the dead cells get +1

@test is_isomorphic(traj_res(res), expected)

end # module
