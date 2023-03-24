module TestPoly 

using Test
using AlgebraicRewriting
using Catlab, Catlab.CategoricalAlgebra,Catlab.Graphs, Catlab.WiringDiagrams, Catlab.Graphics
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
# Graphs
#########


z, g1, ar, loop = Graph(), Graph(1), path_graph(Graph, 2), apex(terminal(Graph))

N=Dict(z=>"Z",g1=>"•",ar=>"•→•")

av = RuleApp(:add_vertex, Rule(id(z), create(g1)))
g2 = homomorphism(Graph(2), ar; monic=true)
de = loop_rule(RuleApp(:del_edge, Rule(g2, id(Graph(2)))))
coin = uniform(2, z)
sched = coin ⋅ (tryrule(av) ⊗ id([z])) ⋅ merge_wires(z) ⋅ de


view_sched(sched, names=N)
G = path_graph(Graph, 4)
res, = apply_schedule(sched, G);
view_traj(sched, res, view_graph; agent=true)


# Query workflow (add loop to each vertex)
##########################################
al = succeed(RuleApp(:add_loop, Rule(id(g1), homomorphism(g1,loop)), g1))
q = Query(:Vertex, g1)

@test_throws AssertionError mk_sched((trace_arg=:O,), (i=:Z,),
  (rule=al, query=q, Z=z,O=g1), quote 
    q1,q2,q3 = query(i,trace_arg)
    trace = rule([q1,q2])
    out = [q3]
    return trace, out
end);


sched = mk_sched((o=:O,), (i=:Z,), Dict(:rule=>al, :query=>q, :Z=>z,:O=>g1), 
quote 
  q1,q2,q3 = query(i,o)
  trace = rule(q2)
  out = [q1,q3]
  return trace, out
end);

view_sched(sched; names=N)
res, = apply_schedule(sched, Graph(3))
view_traj(sched, res, view_graph; agent=true)


# Poly 
######

"""  ____
 ℕ -|    |- String 
 𝔹 -|S=ℕ |- Nothing
     -----
Machine receives a ℕ, it adds it to its internal state + returns nothing 
Machine recieves a 𝔹, it outputs symbol e.g. "True23" where the # is the state.
If the machine has state 10, it returns nothing.
"""
ex_fun(S::Int, w::WireVal) = S == 10 ? MealyRes(S) : ((
  w.wire_id == 1 ? MealyRes(S+w.val, [(nothing,WireVal(2,nothing))]) 
                 : MealyRes(S, [(nothing,WireVal(1,"$(w.val)$S"))])))
m = Mealy(ex_fun, Maybe, 0)
t = BTree(m)
res = first.(t(BTreeEdge[], WireVal(1,3)))
push!(res, only(first.(t(res, WireVal(2,false)))))
push!(res, only(first.(t(res, WireVal(1,7)))))
@test isempty(t(res, WireVal(1,7)))

"""  ____
 ℕ -|    |- String 
 𝔹 -|S=ℕ |- Nothing
     -----
Machine receives a ℕ, it adds it to its internal state + returns nothing 
Machine recieves a 𝔹, it outputs symbol e.g. "True23" where the # is the state.
If the boolean is false, it *also* outputs a nothing.
If the machine has state 10, it returns nothing.
"""
ex_fun(S::Int, w::WireVal) = S == 10 ? MealyRes(S) : ((
  w.wire_id == 1 ? MealyRes(S+w.val, [(1,WireVal(2,nothing))]) 
                 : MealyRes(S, [(1,WireVal(1,"$(w.val)$S"))
                       ] ∪ (w.val ? [] : [(2,WireVal(2,nothing))]))))
m = Mealy(ex_fun, List, 0)
t = BTree(m)
res = first.(t(BTreeEdge[], WireVal(1,3)))
res1,res2 = [vcat(res, r) for r in first.(t(res, WireVal(2,false)))]

push!(res1, only(first.(t(res1, WireVal(1,7)))))
@test isempty(t(res1, WireVal(1,7)))
push!(res2, only(first.(t(res2, WireVal(1,7)))))
@test isempty(t(res2, WireVal(1,7)))

# ℕ → ℕ ⊗ ℕ --- Increment an integer +1 and +2, stateless
inc_fun(::Nothing,w::WireVal; kw...) = 
  MealyRes(nothing, [(p,WireVal(i,w.val+i)) for (i,p) in enumerate([1//3,2//3])])
mi = Mealy(inc_fun, Dist, nothing)

# ℕ → ℕ ⊗ Str --- If even, decrement gas and send out, otherwise print str twice
function some_fun(S::Int,w::WireVal; kw...)  
  if S <= 0 return MealyRes(S)
  elseif w.val % 2 == 0 return MealyRes(S-1,[(1,WireVal(1,w.val))])
  else return MealyRes(S,[(p,WireVal(2, string(w.val))) for p in [1//3,2//3]])
  end
end
ms = Mealy(some_fun, Dist, 5)

wd = WiringDiagram([:N],[:S])
b1 = add_box!(wd, Box(ms,[:N],[:N,:S]))
b2 = add_box!(wd, Box(mi,[:N],[:N,:N]))
i, o = [(f(wd),1) for f in [input_id, output_id]]
add_wires!(wd, Pair[i=>(b1,1), (b1,1)=>(b2,1), (b1,2)=>o, (b2,1)=>(b1,1),(b2,2)=>(b1,1)])
# to_graphviz(wd)


res, = apply_schedule(wd, 0, Dist)
@test length(res) == 8




end # module
