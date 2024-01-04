module Poly 
export List, Maybe, Dist, Mealy, BTreeEdge, BTree, WireVal, MealyRes, PMonad, WireVal, Sim
using StructEquality
using Catlab.WiringDiagrams, Catlab.CategoricalAlgebra

"""
t = Σ_{I:t(1)} y^{t[I]}

I is the summand type 
Operad

(t ◁ WireVal) = [(I,WV)]
"""
struct PMonad 
  I::Type
  η::Function # ∀A, A -> [I×A]
  μ::Function # ∀A, [I×[I×A]]  -> [I×A]
end

Maybe = PMonad(Nothing, 
               x  -> [(nothing,x)],
               xs -> isempty(xs) ? xs : only(xs))

# Accepts a vector of Sim
function joinlist(xs)  
  collect(enumerate(xs))
end
List = PMonad(Int, x -> [(1,x)], joinlist)
function joindist(xs)  
  [(prod([s.edge.t[2] for s in x.steps]), x) for x in xs]
end
Dist = PMonad(Int, x -> [(1,x)], joindist)


"""For an in/output, ΣA, provide wire index + value on wire""" 
@struct_hash_equal struct WireVal 
  wire_id::Int
  val::Any
end

"""Output of a mealy machine"""
@struct_hash_equal struct MealyRes
  newS::Any
  mval::Vector{Tuple{Any,WireVal}}
  msg::String
  MealyRes(newS,mval=Tuple{Any,WireVal}[],msg="") = new(newS,mval, msg)
end 

"""A function that maintains a state"""
struct Mealy
  f::Function # S × WireVal -> S × (t ◁ WireVal)
  t::PMonad
  s0::Any # initial state
  name::String 
  Mealy(f,t,s,n="") = new(f,t,s,string(n))
end
(f::Mealy)(w::WireVal; kw...) = f.f(f.s0, w; kw...)
(f::Mealy)(s::Any,w::WireVal; kw...) = f.f(s, w; kw...)


"""
Data (i,t) which future behavior is contingent on. For convenience, the output 
(o) is stored as well.
"""
@struct_hash_equal struct BTreeEdge 
  i::Union{Nothing,WireVal}
  o::WireVal       
  t::Tuple{Int,Any}
end


"""
Lazily grown behavior tree. Vertices are 
functions ΣA -> t ◁ ΣB. Edges are pairs of (ΣA,tᵢ)
which determine how the tree branches based on the 
input and the monad summand index (i.e. index into 
the list of outputs).

    (f) (f) (f)
       ↖ ↑ ↗
        (f₀)

A vector of keys traverses the BTree.
"""
struct BTree
  S::Dict{Vector{BTreeEdge},Any} # for each node, what is the state
  f::Mealy
  BTree(f::Mealy) = new(Dict(BTreeEdge[]=>f.s0), f)
end

"""
Grow a tree and return the result

ks = list which determines the future behavior.
"""
function (t::BTree)(ks::Vector{BTreeEdge}, w::WireVal; kw...) 
  S = t.S[ks]
  m_res::MealyRes = t.f(S,w; kw...)
  new_S, m_result = m_res.newS, m_res.mval
  map(enumerate(m_result)) do (i,(tᵢ, b))
    new_edge = BTreeEdge(w,b,(i, tᵢ))
    new_pth = vcat(ks,[new_edge])
    if haskey(t.S,new_pth) println("WARNING: REPEAT KEY") end
    t.S[new_pth] = new_S
    new_edge => m_res.msg * " (i=$i, tᵢ=$tᵢ)"
  end 
end


# General polynomial simulations 
################################
@struct_hash_equal struct SimStep 
  desc::String
  edge::BTreeEdge
  inwire::Union{Nothing,Wire}
  outwire::Wire
end

"""ToDO: no 'initial' needed; just use η to get first simstep"""
@struct_hash_equal struct Sim
  steps::Vector{SimStep}
end 
Sim(w::Wire, i::Any, v::Any) = 
  Sim([SimStep("init", BTreeEdge(nothing,WireVal(0,v),(1,i)), nothing, w)])
Base.last(t::Sim) = last(t.steps)
Base.isempty(t::Sim) = isempty(t.steps)
Base.length(t::Sim) = length(t.steps)
Base.getindex(t::Sim, i::Int) = t.steps[i]
add_edge(s::Sim, st::SimStep) = Sim(vcat(s.steps, [st]))
traj_res(s::Sim) = last(s.steps).edge.o.val

"""Get the most recent wire that the simulation is living on"""
function curr_wire(w::WiringDiagram, s::Sim, outer_in_port::Int=-1)
  if isempty(s.steps)
    return only(out_wires(w, Port(input_id(w),OutputPort,outer_in_port)))
  else
    return last(s.steps).outwire
  end
end 
curr_traj(s::Sim) = (isempty(s.steps) ? s.initial : last(s.steps).edge.o).val
sim_edges(s::Sim, boxid::Int) = 
  BTreeEdge[e.edge for e in s.steps[2:end] if e.inwire.target.box == boxid]

"""Replace all boxes in a WD with BTrees"""
function apply_schedule(w_::WiringDiagram,g::Any,t::PMonad=Maybe; 
                        in_port=1, steps=-1)
  # Replace boxes of Mealy machines with BTrees
  w = WiringDiagram([],[])
  copy_parts!(w.diagram, w_.diagram)
  w.diagram[:box_type] = Box{BTree}
  w.diagram[:value] = BTree.(w.diagram[:value])
  # Initialize queue of simulations to track
  iw = only(out_wires(w, Port(input_id(w),OutputPort, in_port)))
  squeue = [Sim(iw,i,v) for (i,v) in t.η(g)] # [Sim(WireVal(in_port, g))] # start with a single simulation 'token'
  results = [Sim[] for _ in output_ports(w)] 
  counter = 0
  # Main loop
  while !isempty(squeue)
    traj = pop!(squeue)
    steps -= 1; counter += 1
    if steps == 0 
      if length(results) == 1 
        push!(results[1], traj)
        @debug "TIMEOUT"
        continue
      else 
        error("timeout! multiple possible outputs") 
      end
    end
    wi = last(traj.steps).outwire
    b = wi.target.box
    if wi.target.box == output_id(w)
      push!(results[wi.target.port], traj)
    else 
      # info 
      @debug "Step $counter (Box#$(b).$(wi.target.port): $(box(w,b).value.f.name))" 
      if steps > 0 "($steps STEPS REMAINING )" end
      if length(squeue) > 0 @debug "($(length(squeue)) queued)" end
        prepend!(squeue, apply_traj_step(w, traj, wi;)) # DFS
    end
  end 
  return t.μ.(results)  # apply monadic unit / multiplication to results
end

function apply_traj_step(w::WiringDiagram,t::Sim, wi::Wire;)
  cw = wi.target
  btree,i = box(w,cw.box).value, cw.port
  traj_val = WireVal(i, curr_traj(t))
  es = sim_edges(t,cw.box)
  bres = btree(es, traj_val)
  map(bres) do (new_edge, msg)
    ow = only(out_wires(w, Port(cw.box,OutputPort,new_edge.o.wire_id)))
    add_edge(t, SimStep(msg, new_edge, wi, ow))
  end 
end

  
end # module
