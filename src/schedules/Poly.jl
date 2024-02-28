"""
Mealy machines (augmented with monadic output) are a user-friendly format for
specifying a behavior tree. Behavior trees in general are not finitely 
expressible, but we focus on trees which can be lazily generated by functions.

Although it is conceptually simple to think of a single set of "input doors" out 
"output doors" to enter/leave the Mealy machine, such that a Mealy machine has 
type A → B, we use Σᵢ Aᵢ → Σⱼ Bⱼ, where Aᵢ and Bⱼ are Julia types. This allows 
us to represent a Mealy machine with (Int + String)-many input doors, for 
example.
"""
module Poly
export List, Maybe, Dist, Mealy, BTreeEdge, BTree, WireVal, MealyRes, PMonad, 
       WireVal, Traj, TrajStep, Simulator

using StructEquality, DataStructures
using Catlab.WiringDiagrams, Catlab.CategoricalAlgebra

# Polynomial Monads 
###################
"""
Quotes in this docstring and others taken from David Spivak:
https://topos.site/blog/2023/09/powers-of-polynomial-monads/#exponentiating-monads

"A polynomial monad is a polynomial functor t with coherent maps η: y → t and 
μ: t ◁ t → t.

Polynomial monads can be thought of as offering compositional (possibly labeled) 
packages with some number of slots. The compositionality of this packaging says 
that (via the monad unit) we know how to package up a given element of any set, 
and that (via the monad multiplication) we can take a package of packages and 
simplify it to a single package."

We consider monads t of the form: t = Σ_{i ∈ t(1)} y^{t[i]}

I is the type of labels, e.g. probability weights.
"""
struct PMonad{I}
  η::I # ∀A, A -> [I×A]
  μ::Function # ∀A, [I×[I×A]]  -> [I×A]
end

function mu(m::PMonad{I}, vs::Vector{Pair{I, Vector{I}}})::Vector{Tuple{Int,Int,I}} where I 
  m.μ(vs)
end
# Common monads
#--------------
"""
"The Maybe monad, y+1, consists of two packages, one with one slot and the 
other with no slots."
"""
Maybe = PMonad{Nothing}(nothing,
  xs -> isempty(xs) ? Tuple{Int,Int,Nothing}[] : [(1, 1,nothing)])

"""
"The list monad returns the set of packages labeled with a natural number N, 
each of which has N-many slots."
"""
List = PMonad{Nothing}(nothing, xs->vcat(last.(xs)...))

# function joinlist(xs)  
#   collect(enumerate(xs))
# end


"""
"The lotteries monad returns the set of packages labeled with a lottery 
(a natural number N and a probability distribution on it) and again containing 
N-many slots."
"""
function joindist(xs)  
  [(prod([s.edge.t[2] for s in x.steps]), x) for x in xs]
end

Dist = PMonad{Rational{Int}}(1//1, joindist)

"""
Writer monad
"""
joinstr(x) = error("HERE")
Writer = PMonad{String}("", joinstr)


# Mealy Machines Σᵢ Aᵢ → Σⱼ Bⱼ
#############################

"""For an in/output, Σᵢ Aᵢ, provide wire index + value on wire""" 
@struct_hash_equal struct WireVal 
  wire_id::Int
  val::Any
end

getvalue(w::WireVal) = w.val

"""
Output of a Mealy machine

newS - The new state of the Mealy machine 
mval - outputs along with their monadic values (e.g. probability weights)
msg  - A message reporting something about the computation 
"""
@struct_hash_equal struct MealyRes{S, I}
  newS::S
  mval::Vector{Tuple{I, WireVal}}
  msg::String
  MealyRes(newS::S, mval::Vector{Tuple{I, WireVal}}, msg="") where {S, I} = 
    new{S, I}(newS, mval, msg)
end 

MealyRes(newS, I::Type, msg="") = MealyRes(newS, Tuple{I, WireVal}[], msg)
getvalue(w::MealyRes) = w.mval


"""
A function that maintains a state (initially s0) and has monadic output for some 
polynomial monad t.

The function f must be of type S × WireVal → S × (t ◁ WireVal) 
  
                                (i.e. S × Wireval → MealyRes)
"""
struct Mealy{S, I}
  f::Function
  in_types::Vector{Type}
  out_types::Vector{Type}
  t::PMonad{I}
  s0::S 
  name::String 
  Mealy(f, in_types, out_types, t::PMonad{I}, s::S, n="") where {S, I} = 
    new{S, I}(f, in_types, out_types, t, s, string(n))
end

Base.show(io::IO, m::MIME"text/plain", mm::Mealy) = show(io, m, mm.name)

Base.string(machine::Mealy) = machine.name

function (f::Mealy{S,I})(w::WireVal; kw...)::MealyRes{S,I} where {S,I} 
  f.f(f.s0, w; kw...)
end

function (f::Mealy{S,I})(s::S, w::WireVal; kw...)::MealyRes{S,<:I} where {S,I}
  w.val isa f.in_types[w.wire_id] || error("Bad input type $w")
  res = f.f(s, w; kw...)
  for wv in last.(res.mval)
    wv.val isa f.out_types[wv.wire_id] || error("Bad output type $wv")
  end
  res
end

# Behavior trees 
################

"""
Lazily grown behavior tree induced by a Mealy machine. The future behavior is 
dictated by the inputs seen thus far (i.e. a vector of WireVals).

Each vertex is identified by a sequence of inputs and has a state of the Mealy 
machine associated with it.

Each nonempty sequence of inputs has a MealyRes associated with it.
"""
struct BTree{S}
  result_cache::Dict{Vector{WireVal}, MealyRes{S}} # for each node
  f::Mealy{S}
  BTree(f::Mealy{S}) where S = 
    new{S}(Dict{Vector{WireVal},MealyRes}(), f)
end

function get_state(t::BTree{S}, inputs::Vector{WireVal})::S where S
  if isempty(inputs)
    t.f.s0
  else
    t.result_cache[inputs].newS
  end
end

getvalue(t::BTree, xs::Vector{WireVal}) = getvalue(t.result_cache[xs])

Base.haskey(t::BTree, xs::Vector{WireVal}) = haskey(t.result_cache, xs)

"""Grow a tree and return the result."""
function (t::BTree)(ks::Vector{WireVal}; kw...)
  haskey(t, ks) && @debug "WARNING: REPEAT KEY"
  old..., new = ks # ks cannot be empty
  isempty(old) || haskey(t, old) || t(old) # recursively compute earlier subsequences
  S = get_state(t, old)
  t.result_cache[ks] = t.f(S, new; kw...)
  getvalue(t, ks)
end

# # General polynomial simulations 
# ################################
function traj_res end

"""
Equips a wiring diagram description of a simulator with mutable data structures
(now behavior trees for each box, but possibly incremental homomorphism caches 
in the future). Requires that all the boxes of the WiringDiagram be convertable 
to BTrees.
"""
struct Simulator
  d::WiringDiagram
  trees::Vector{BTree}
  function Simulator(wd::WiringDiagram)
    # to do, cast all PMonads to the lowest common denominator
    new(wd, BTree.(wd.diagram[:value]))
  end
end

"""
A trajectory step is a box being fed a particular value

This only makes sense with reference to a WiringDiagram which `box` refers to.
"""
@struct_hash_equal struct TrajStep{I}
  desc::String
  box::Int
  inwire::WireVal
  outwire::WireVal
  mval::I
end

@struct_hash_equal struct Traj{I}
  inwire::Wire
  initial::Any
  steps::Vector{TrajStep{I}}
end

Base.isempty(t::Traj) = isempty(t.steps)
Base.length(t::Traj) = length(t.steps)
Base.last(t::Traj) = last(t.steps)

"""Append without mutating"""
add_edge(s::Traj{I}, st::TrajStep{I}) where {I} = 
  Traj(s.inwire, s.initial, TrajStep{I}[s.steps; st])

curr_path(t::Traj) = WireVal[s.inwire for s in t.steps]

"""Current state of the world"""
curr_state(t::Traj) = isempty(t)  ? t.initial : getvalue(last(t).outwire)

"""Get the wire which the traj is currently on"""
function currwire(sim::Simulator, t::Traj)
  if isempty(t)
    t.inwire
  else     
    p = Port(last(t).box, OutputPort, last(t).outwire.wire_id)
    out_wires(sim.d, p) |> only
  end
end


"""
In theory applying a schedule should result in a list of ACSets associated with 
out ports and monad labels (e.g. probabilities), and if one were to want to 
recover the trajectory of the output one would have to use a Writer monad 
of some sort. For simplicity, the application of a schedule will simply return 
the trajectories themselves (monadic multiplication could in principle condense 
this output to the pure output).
"""
function apply_schedule(sim::Simulator, g::Any, ::PMonad{I}=Maybe; 
                        in_port=1, steps=-1) where I
  # Initialize queue of simulations to track
  iw = only(out_wires(sim.d, Port(input_id(sim.d),OutputPort, in_port)))
  squeue = [Traj(iw, g, TrajStep{I}[])] # start with a single simulation 'token'
  results = Traj[]
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
    wi = currwire(sim, traj)
    tgt = wi.target
    b = tgt.box
    bx = box(sim.d, b)
    if b == output_id(sim.d)
      push!(results, traj)
    else 
      @debug "Step $counter (Box#$(b).$(tgt.port): $(bx.value.name)) $(curr_state(traj))" 
      steps > 0 && @info "($steps STEPS REMAINING )"
      length(squeue) > 0 && @debug "($(length(squeue)) queued)"
      prepend!(squeue, apply_traj_step(sim, traj, wi;)) # DFS
    end
  end
  results
end

"""
A particular trajectory enters a box. Out of the box comes a 
list of trajectories.
"""
function apply_traj_step(sim::Simulator, t::Traj, wi::Wire;)::Vector{Traj}
  cw = wi.target
  btree = sim.trees[cw.box]
  in_wval = WireVal(cw.port, curr_state(t))
  new_pth = WireVal[curr_path(t); in_wval]
  btree(new_pth)
  map(btree.result_cache[new_pth].mval) do (monad_label, wval)
    add_edge(t, TrajStep("", cw.box, in_wval, wval, monad_label))
  end 
end
  
end # module
