module TestEval

using Test
using Catlab, Catlab.Theories, Catlab.WiringDiagrams, Catlab.Graphics
using Catlab.Graphs, Catlab.CategoricalAlgebra
using Catlab.Graphics: to_graphviz_property_graph

using AlgebraicRewriting
using Luxor
using PrettyTables


# Graph + agent viewer 
######################
view_graph(a::Graph, path=tempname()) = view_graph(create(a), path)

function view_graph(a::ACSetTransformation, path=tempname())
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

z, g1, ar, loop = Graph(), Graph(1), path_graph(Graph, 2), apex(terminal(Graph))

N=Names(Dict("Z"=>z,"•"=>g1))
@test length(N) == 2
N["•→•"] = ar
Dot, A = Symbol.([N[g1],N[ar]]) 

av = RuleApp(:add_vertex, Rule(id(z), create(g1)))
g2 = homomorphism(Graph(2), ar; monic=true)
de = loop_rule(RuleApp(:del_edge, Rule(g2, id(Graph(2)))))
coin = uniform(2, z)
sched = coin ⋅ (tryrule(av) ⊗ id([z])) ⋅ merge_wires(z) ⋅ de

# view_sched(sched, name="Simple schedule", names=N)
G = path_graph(Graph, 4)
res, = apply_schedule(sched, G);
# view_traj(sched, res, view_graph; agent=true, names=N)

# Query workflow (add loop to each vertex)
##########################################
al = succeed(RuleApp(:add_loop, Rule(id(g1), homomorphism(g1,loop)), g1))
q = Query(:Vertex, g1)

bad_sched =mk_sched((trace_arg=Dot,), (i=:Z,), N, (rule=al, query=q), quote 
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
end)

typecheck(sched)

# view_sched(sched; names=N)
res, = apply_schedule(sched, Graph(3))
# view_traj(sched, res, view_graph; agent=true, names=N)


# Dependent query workflow 
# (flip to add loop to each vertex downstream of tgt, then add edge out of src)
##############################################################################
s_hom, t_hom = [ACSetTransformation(g1,ar; V=[i]) for i in 1:2]

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

# view_sched(sched; names=N)

G = @acset Graph begin V=5; E=4; src=[1,2,2,5];tgt=[2,3,4,2] end
arr_start = homomorphism(ar, G; initial=(V=[1,2],))
res, = apply_schedule(sched, arr_start);
# view_traj(sched, res, view_graph; agent=false)
# view_traj(sched, res, view_graph; agent=true, names=N)


# For-loop: add 3 loops
#######################
sched = for_schedule(maybe_add_loop ⋅ merge_wires(g1), 3)
res, = apply_schedule(sched, id(g1));
# view_sched(sched; names=N)


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

"""
ASCII example
"""
function view_life(X::LG, path=tempname())
  coords, n, m = get_coords(X)
  mat = pretty_table(String, reduce(hcat,map(1:n) do i 
    map(1:m) do j 
      l = X[coords[(i,j)],:live] ? "O" : "X"
      return "$(l)$(X[coords[(i,j)],:eng])"
    end
  end); show_header=false, tf=tf_markdown)
  open(path, "w") do io write(io, mat) end
  return mat
end

"""Assume it's rectangular"""
function get_coords(X::LG)
  res = Union{Nothing,Tuple{Int,Int}}[nothing for _ in parts(X,:Cell)]
  function get_coord!(c)
    if !isnothing(res[c]) return res[c] end 
    n_e, w_e = [X[c, Symbol("cell_$s")] for s in "NW"]
    neighbor_n = incident(X, n_e, :cell_S)
    if !isempty(neighbor_n)
      i, j = get_coord!(only(neighbor_n))
      res[c] = (i+1,j)
      return res[c]
    else
      neighbor_w = incident(X, w_e, :cell_E)
      if !isempty(neighbor_w)
        i, j = get_coord!(only(neighbor_w))
        res[c] = (i,j+1)
        return res[c]
      else
        res[c] = (1,1)
        return res[c]
      end
    end 
  end
  get_coord!.(parts(X, :Cell))
  n, m = [maximum(f.(res)) for f in [first,last]]
  return Dict(v=>i for (i,v) in enumerate(res)), n, m
end

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
inc_E_rule = RuleApp(:incE,inc_E,homomorphism(Cell,inc_E_)) |> tryrule

# Assemble a schedule 
sched = agent(inc_E_rule, Cell, ret=Cell)


# Demonstrate on a 2 x 2 grid:  L D
#                               L D
G = @acset LG begin Cell=4; V=9; E=12
  src=[1,1,2,2,3,4,4,5,5,6,7,8]; tgt=[2,4,3,5,6,5,7,6,8,9,8,9]; 
  cell_W=[2,4,7,9]; cell_E=[4,5,9,10]; cell_S=[1,3,6,8]; cell_N=[6,8,11,12]
  live=[true,false,true,false]; eng=[1,10,100,1000]
end

res, = apply_schedule(sched, G)

expected = deepcopy(G)
expected[:eng] = [1,11,100,1001] # the dead cells get +1

@test is_isomorphic(traj_res(traj_res(res)), expected)

# view_traj(sched, res, view_life; agent=false)

end # module
