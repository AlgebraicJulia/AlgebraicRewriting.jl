using AlgebraicRewriting
using Catlab, Catlab.Graphs, Catlab.CategoricalAlgebra, Catlab.Theories
import Catlab.Graphics: to_graphviz
using Catlab.Graphics.Graphviz: Attributes, Statement, Node, Edge, Digraph
using PrettyTables
using Luxor

"""
The game of life has two rules: one which turns living things dead, and one 
that brings dead things to life. We model the terrain as a symmetric graph:
cells are vertices. Neighboring cells have edges between them.

Implementationwise, if we are going to update 
cells one at a time, we must keep track of two bits of information (the cell's 
living status for the *current* timestep and whether it will be alive in the 
*next* timestep). Thus we need helper rule to overwrite the "current" 
life status with the "next" life status at the end of each timestep.
"""

# Schema 
########

"""
`curr` and `next` pick out subsets of V which are marked as currently alive or 
to be alive in the next timestep.
"""
@present SchLife <: SchSymmetricGraph begin
  (Curr, Next)::Ob
  curr::Hom(Curr, V)
  next::Hom(Next, V)
end
@present SchLifeCoords <: SchLife begin
  Coords::AttrType
  coords::Attr(V, Coords)
end
@acset_type Life(SchLife) <: AbstractSymmetricGraph
@acset_type AbsLifeCoords(SchLifeCoords) <: AbstractSymmetricGraph
const LifeCoords = AbsLifeCoords{Tuple{Int,Int}}
F = Migrate(
  Dict(x => x for x in Symbol.(generators(SchLife, :Ob))),
  Dict(x => x for x in Symbol.(generators(SchLife, :Hom))), LifeCoords; delta=false)

# Helper 
########

# Visualization 
function view_life(f::ACSetTransformation, pth=tempname())
  v = collect(f[:V])
  view_life(codom(f), pth; star=isempty(v) ? nothing : only(v))
end
function view_life(X::Life, pth=tempname(); star=nothing)
  pg = PropertyGraph{Any}(; prog="neato", graph=Dict(),
    node=Dict(:shape => "circle", :style => "filled", :margin => "0"),
    edge=Dict(:dir => "none", :minlen => "1"))
  add_vertices!(pg, nparts(X, :V))
  for v in vertices(X)
    set_vprop!(pg, v, :fillcolor, isempty(incident(X, v, :curr)) ? "red" : "green")
    if !isempty(incident(X, v, :next))
      set_vprop!(pg, v, :penwidth, "4.0")
    end
    set_vprop!(pg, v, :label, star == v ? "*" : "")
  end
  for e in filter(e -> X[e, :inv] > e, edges(X))
    add_edge!(pg, X[e, :src], X[e, :tgt])
  end
  G = to_graphviz(pg)
  open(pth, "w") do io
    show(io, "image/svg+xml", G)
  end
  G
end
function view_life(X::LifeCoords, pth=tempname(); star=nothing)
  n = Int(sqrt(nparts(X, :V)))
  coords = Dict([(i, j) => findfirst(==((i, j)), X[:coords])
                 for (i, j) in Iterators.product(1:n, 1:n)])
  mat = pretty_table(String, reduce(hcat, map(1:n) do i
      map(1:n) do j
        c, x = [!isempty(incident(X, coords[(i, j)], x)) for x in [:curr, :next]]
        res = c ? (x ? "O" : "o") : (x ? "X" : "x")
        return res * ((star == coords[(i, j)]) ? "." : "")
      end
    end); show_header=false, tf=tf_markdown)
  open(pth, "w") do io
    write(io, mat)
  end
  return mat
end

# Constructions for Life ACSets / maps between them
Next() = @acset Life begin
  V = 1
  Next = 1
  next = 1
end
Curr() = @acset Life begin
  V = 1
  Curr = 1
  curr = 1
end
to_next() = homomorphism(Life(1), Next())
to_curr() = homomorphism(Life(1), Curr())

"""Construct a cell connected to n living neighbors"""
function living_neighbors(n::Int; alive=false)
  X = Life(1)
  if alive
    add_part!(X, :Curr, curr=1)
  end
  for _ in 1:n
    v = add_part!(X, :V)
    add_part!(X, :Curr, curr=v)
    add_edge!(X, v, 1)
  end
  return X
end

# Initialization of LifeCoords
function make_grid(curr::AbstractMatrix, next=nothing)
  n, m = size(curr)
  n == m || error("Must be square")
  X, coords = LifeCoords(), Dict()
  for i in 1:n
    for j in 1:n
      coords[i=>j] = add_vertex!(X; coords=(i, j))
      if Bool(curr[i, j])
        add_part!(X, :Curr, curr=coords[i=>j])
      end
      if !isnothing(next) && Bool(next[i, j])
        add_part!(X, :Curr, curr=coords[i=>j])
      end
    end
  end
  for i in 1:n
    for j in 1:n
      if i < n
        add_edge!(X, coords[i=>j], coords[i+1=>j])
      end
      if j < n
        add_edge!(X, coords[i=>j], coords[i=>j+1])
      end
      if i < n && j < n
        add_edge!(X, coords[i=>j], coords[i+1=>j+1])
      end
      if i < n && j > 1
        add_edge!(X, coords[i=>j], coords[i+1=>j-1])
      end
    end
  end
  return X
end
make_grid(n::Int, random=false) = make_grid((random ? rand : zeros)(Bool, (n, n)))

# Rules 
#######

# A dead cell becomes alive iff exactly 3 living neighbors
#---------------------------------------------------------
BirthP1 = living_neighbors(3) # must have 3 neighbors
BirthN1 = living_neighbors(4) # forbid the cell to have 4 neighbors
BirthN2 = Curr() # forbid the cell to be alive (i.e. it's currently dead)
BP1, BN1, BN2 = homomorphism.(Ref(Life(1)), [BirthP1, BirthN1, BirthN2])
bac = [AppCond(BP1; monic=true), AppCond.([BN1, BN2], false; monic=true)...]
Birth = Rule(id(Life(1)), to_next(); ac=bac)

# A living cell stays alive iff 2 or 3 living neighbors
#------------------------------------------------------
PersistR = @acset Life begin
  V = 1
  Curr = 1
  Next = 1
  curr = 1
  next = 1
end
PersistP1 = living_neighbors(2; alive=true)
PersistN1 = living_neighbors(4; alive=true)
DR, DP1, DN1 = homomorphism.(Ref(Curr()), [PersistR, PersistP1, PersistN1])
pac = [AppCond(DP1; monic=true), AppCond(DN1, false; monic=true)]
Persist = Rule(id(Curr()), DR; ac=pac)

ClearCurr = Rule(to_curr(), id(Life(1))) # remove "Curr" status
ClearNext = Rule(to_next(), id(Life(1))) # remove "Next" status
CopyNext = Rule(to_next(), to_curr())   # Copy "Next" to "Curr"

rules = [:Birth => Birth, :Persist => Persist, :ClearCurr => ClearCurr,
  :ClearNext => ClearNext, :CopyNext => CopyNext]
# Schedule
##########

# All rules have interface of a single distinguished cell.
# Never distinguish control flow of successful vs unsuccessful application
rBirth, rPersist, rClearCurr, rClearNext, rCopyNext =
  [tryrule(RuleApp(n, r, Life(1))) for (n, r) in rules]

update_next = agent(rBirth ⋅ rPersist, Life(1); n=:Cell)
next_step = agent(compose(rClearCurr, rCopyNext, rClearNext), Life(1); n=:Cell)
life(n::Int) = for_schedule(update_next ⋅ next_step, n) |> F
const L = life(1)

G = make_grid([1 0 1 0 1; 0 1 0 1 0; 0 1 0 1 0; 1 0 1 0 1; 1 0 1 0 1])

res, = apply_schedule(L, G; steps=1000)
traj = last(res).edge.o.val

view_life(i, traj) = view_life(traj.steps[i].world)

# view_traj(L, res, view_life; agent=true)
