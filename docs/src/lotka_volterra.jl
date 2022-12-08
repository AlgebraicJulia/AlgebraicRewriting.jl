using Catlab, Catlab.Theories, Catlab.CategoricalAlgebra, Catlab.Graphs, 
      Catlab.Graphics, Catlab.WiringDiagrams
using AlgebraicRewriting
using Random, Test, StructEquality

Random.seed!(1234);

const hom = AlgebraicRewriting.homomorphism
const R = AlgebraicRewriting.RuleSchedule

using Catlab.Graphics.Graphviz: Attributes, Statement, Node
using Catlab.Graphics.Graphviz

using AlgebraicRewriting.Variables: FinDomDefaultDict 
import Catlab.CategoricalAlgebra: left, right

abstract type Direction end 
begin
  @struct_hash_equal struct North <: Direction end 
  @struct_hash_equal struct South <: Direction end 
  @struct_hash_equal struct East <: Direction end 
  @struct_hash_equal struct West <: Direction end 
  show(io,::North) = show(io, :N)
  show(io,::South) = show(io, :S)
  show(io,::East) = show(io, :E)
  show(io,::West) = show(io, :W)
  right(::North) = East()
  right(::East) = South()
  right(::South) = West()
  right(::West) = North()
  left(::North) = West()
  left(::East) = North()
  left(::South) = East()
  left(::West) = South()
end

"""
Grass = 0 means alive grass, whereas grass > 0 represent a counter of time until
the grass is alive.

Sheeps and wolves have position and direction, so we assign each an *edge*. We
assume a convention where the location of the something is the edge SOURCE.

Dir is an attribute which can take values :N, :E, :W, and :S.
"""
@present TheoryLV <: SchGraph begin
  (Sheep,Wolf)::Ob
  sheep_loc::Hom(Sheep, V)
  wolf_loc::Hom(Wolf, V)

  (Dir,Eng)::AttrType
  grass_eng::Attr(V, Eng)
  sheep_eng::Attr(Sheep, Eng)
  wolf_eng::Attr(Wolf, Eng)
  sheep_dir::Attr(Sheep, Dir)
  wolf_dir::Attr(Wolf, Dir)
  dir::Attr(E, Dir)
end


to_graphviz(TheoryLV; prog="dot")

@acset_type LV_Generic(TheoryLV) <: HasGraph
VED, VEI = Union{Var,Expr,Direction}, Union{Var,Expr,Int}
const LV = LV_Generic{VED, VEI}

F = FinFunctor(
  Dict([:Sheep => :Wolf, :Wolf => :Sheep, :V=>:V, :E=>:E,:Dir=>:Dir, :Eng=>:Eng]),
  Dict([:sheep_loc=>:wolf_loc, :wolf_loc=>:sheep_loc,
        :sheep_eng=>:wolf_eng, :wolf_eng=>:sheep_eng,:grass_eng =>:grass_eng,
        :sheep_dir=>:wolf_dir, :wolf_dir=>:sheep_dir,
        :src=>:src,:tgt=>:tgt,:dir=>:dir]),
  TheoryLV, TheoryLV
)
F = DeltaMigration(F, LV, LV)

"""
Create a nxn grid with periodic boundary conditions. Edges in each cardinal
direction originate at every point


(i,j+1) -> (i+1,j+1) -> ...
  ↑          ↑
(i,j)   -> (i+1,j)   -> ...

"""
function create_grid(n::Int)
  lv = LV()
  coords = Dict()
  # Initialize grass 50% green, 50% uniformly between 0-30
  for i in 0:n-1
    for j in 0:n-1
      coords[i=>j] = add_part!(lv, :V; grass_eng=max(0,rand(-30:30)))
    end
  end
  for i in 0:n-1
    for j in 0:n-1
      add_part!(lv, :E; src=coords[i=>j], tgt=coords[mod(i+1,n)=>j], dir=East())
      add_part!(lv, :E; src=coords[i=>j], tgt=coords[mod(i-1,n)=>j], dir=West())
      add_part!(lv, :E; src=coords[i=>j], tgt=coords[i=>mod(j+1,n)], dir=North())
      add_part!(lv, :E; src=coords[i=>j], tgt=coords[i=>mod(j-1,n)], dir=South())
    end
  end
  c = fill(0=>0, nv(lv))
  for (k,v) in collect(coords) c[v] = k end
  return lv, c
end

g, c = create_grid(2)

"""
`n` is the length of the grid.
`sheep` and `wolves` are the fraction of spaces that are 
populated with that animal
"""
function initialize(n::Int, sheep::Float64, wolves::Float64)
  grid, coords = create_grid(n)
  args = [(sheep, :Sheep, :sheep_loc, :sheep_eng, :sheep_dir),
          (wolves, :Wolf, :wolf_loc, :wolf_eng, :wolf_dir)]
  for (n_, name, loc, eng, d) in args
    for _ in 1:round(Int,n_*n^2)
      dic = Dict([eng => 5, loc => rand(vertices(grid)),
                  d => rand([North(),East(),South(),West()])])
      add_part!(grid, name; dic...)
    end
  end
  return grid, coords
end


supscript_d = Dict(['1'=>'¹', '2'=>'²', '3'=>'³', '4'=>'⁴', '5'=>'⁵',
                    '6'=>'⁶', '7'=>'⁷', '8'=>'⁸', '9'=>'⁹', '0'=>'⁰',
                    'x'=>'ˣ', 'y'=>'ʸ','z'=>'ᶻ','a'=>'ᵃ','b'=>'ᵇ','c'=>'ᶜ',
                    'd'=>'ᵈ'])
supscript(x::String) = join([get(supscript_d, c, c) for c in x])

"""Visualize a LV"""
function Graph(p::LV; positions=positions, name="G", title="")
  pstr = ["$(i),$(j)!" for (i,j) in positions]
  stmts = Statement[]
    for s in 1:nv(p)
        gv = p[s, :grass_eng]
        col = gv  == 0 ? "lightgreen" : "tan"
        push!(stmts,Node("v$s", Attributes(
                    :label=>gv == 0 ? "" : string(gv), #"v$s",
                    :shape=>"circle",
                    :color=> col, :pos=>pstr[s])))
    end
  d = Dict([East()=>(1,0),North()=>(0,1), South()=>(0,-1),West()=>(-1,0),])

  args = [(:true,:Wolf,:wolf_loc,:wolf_eng,:wolf_dir),
          (false, :Sheep, :sheep_loc, :sheep_eng,:sheep_dir)]

  for (is_wolf, prt, loc, eng, dr) in args
    for w in parts(p, prt)
      e = only(incident(p,p[w,loc], :src) ∩ incident(p,p[w,dr], :dir))
      s = src(p,e)
      dx, dy = d[p[e, :dir]]
      (sx,sy) = positions[s]

      L, R = 0.25, 0.1
      wx = sx+L*dx+R*rand()
      wy = sy+L*dy+R*rand()
      ID = "$(is_wolf ? :w : :s)$w"
      append!(stmts,[Node(ID, Attributes(
        :label=>"$w"*supscript("$(p[w,eng])"),
        :shape=>"square", :width=>"0.3px", :height=>"0.3px", :fixedsize=>"true",
        :pos=>"$(wx),$(wy)!",:color=> is_wolf ? "red" : "lightblue"))])
    end
  end

  g = Graphviz.Digraph(name, Statement[stmts...]; prog="neato",
        graph_attrs=Attributes(:label=>title, :labelloc=>"t"),
        node_attrs=Attributes(:shape=>"plain", :style=>"filled"))
  return g
end

i1,i2 = initialize(2,0.5,0.5)


# RULES
#######

# Rotating
#---------

shift_l = @acset LV begin
  Sheep=1; V=1; sheep_loc=1; 
  sheep_eng=[Var(:_0)]; grass_eng=[Var(:_1)]
  sheep_dir=[Var(:d)]; 
end

shift_i = @acset LV begin
  Sheep=1; V=1; sheep_loc=1; 
  sheep_eng=[Var(:_0)]; grass_eng=[Var(:_1)]
  sheep_dir=[Var(:d2)]; 
end

shift_il = hom(shift_i, shift_l; bindvars=true)

"""Generate a rule that rotates a sheep to the left or the right"""
function shift(lft::Bool=true)
  lr = lft ? :(left(d)) : :(right(d))
  r = deepcopy(shift_i)
  set_subpart!(r, 1, :sheep_dir, lr)
  ir = hom(shift_i,r; bindvars=true)
  Rule(shift_il, ir)
end

sheep_rotate_l = RuleSchedule("sheep_left", shift())
sheep_rotate_r = RuleSchedule("sheep_right", shift(false))
wolf_rotate_l = RuleSchedule("wolf_left", F(shift()))
wolf_rotate_r = RuleSchedule("wolf_right", F(shift(false)))

# we can imagine executing these rules in sequence or in parallel
(sheep_rotate_l⋅sheep_rotate_r) ⊗ (wolf_rotate_l⋅wolf_rotate_r) |> to_graphviz


# Moving forward
#---------------
s_move_forward_l = @acset LV begin
  Sheep=1; V=2; E=1; sheep_loc=1;
  src=1; tgt=2; dir=[Var(:z)]; 
  grass_eng=Var.([:_1,:_2])
  sheep_dir=[Var(:z)]; sheep_eng=[Var(:x)]
end

s_move_forward_i = deepcopy(s_move_forward_l)
rem_part!(s_move_forward_i, :Sheep, 1)

s_move_forward_r = deepcopy(s_move_forward_i)
add_part!(s_move_forward_r, :Sheep; sheep_loc=2, sheep_eng=:(x-1), sheep_dir=Var(:z))

s_move_n = deepcopy(s_move_forward_l)
set_subpart!(s_move_n, 1, :sheep_eng, 0)

sheep_move_forward_rule = Rule(
  hom(s_move_forward_i, s_move_forward_l; monic=true),
  hom(s_move_forward_i, s_move_forward_r; monic=true),
  [NAC(hom(s_move_forward_l, s_move_n; monic=true,bindvars=true))]
)

sheep_move_forward = RuleSchedule("sheep move forward", sheep_move_forward_rule)
wolf_move_forward = RuleSchedule("wolf move forward", F(sheep_move_forward_rule))

# Eat grass + 4eng
#-----------------
s_eat_l = @acset LV begin
  Sheep=1; Eng=2; V=1; sheep_loc=1;  grass_loc=[Var(:d)]; 
  grass_eng=[0]; sheep_eng=[Var(:e)]; sheep_dir=[Var(:_1)]
end

s_eat_i = deepcopy(s_eat_l)
set_subpart!(s_eat_i, 1, :grass_eng, Var(:ge))
set_subpart!(s_eat_i, 1, :sheep_eng, Var(:se))

s_eat_r = deepcopy(s_eat_i)
set_subpart!(s_eat_r, 1, :grass_eng, 30)
set_subpart!(s_eat_r, 1, :sheep_eng, :(e+4))

sheep_eat = RuleSchedule("Sheep eat", 
  Rule(hom(s_eat_i, s_eat_l; bindvars=true), 
       hom(s_eat_i, s_eat_r; bindvars=true)))

# Eat sheep + 20 eng
#-------------------
w_eat_l = @acset LV begin
  Sheep=1; Wolf=1; V=1; grass_eng=[Var(:_0)]
  sheep_dir=[Var(:_1)]; wolf_dir=[Var(:_2)]; 
  sheep_eng=[Var(:_3)]; wolf_eng=[Var(:e)]
  sheep_loc=1; wolf_loc=1
end

w_eat_i = @acset LV begin
  Wolf=1; V=1; grass_eng=[Var(:_0)]
  wolf_dir=[Var(:_2)]; wolf_eng=[Var(:e)]; wolf_loc=1
end

w_eat_r = deepcopy(w_eat_i)
set_subpart!(w_eat_r, 1, :wolf_eng, :(e+20))

wolf_eat = RuleSchedule("Wolf eat", 
  Rule(hom(w_eat_i, w_eat_l; bindvars=true), 
       hom(w_eat_i, w_eat_r; bindvars=true)))

# Die if 0 eng
#-------------
s_die_l = @acset LV begin
  Sheep=1; V=1; grass_eng=[Var(:_1)]
  sheep_eng=[0]; sheep_loc=1; sheep_dir=[Var(:_0)]
end
s_die_r = @acset LV begin V=1; grass_eng=[Var(:_1)] end
sheep_die_rule = Rule(hom(s_die_r, s_die_l), id(s_die_r))
sheep_starve = RuleSchedule("Sheep starve", sheep_die_rule)
wolf_starve = RuleSchedule("Wolf starve", F(sheep_die_rule))

# reproduction
#-------------
s_reprod_l =  @acset LV begin
  Sheep=1; V=1; sheep_loc=1; grass_eng=[Var(:_1)]
  sheep_dir=[Var(:_2)]; sheep_eng=[Var(:a)]; 
end

s_reprod_i = @acset LV begin V=1; grass_eng=[Var(:_1)] end

s_reprod_r =  @acset LV begin
  Sheep=2; V=1; sheep_loc=1; grass_eng=[Var(:_1)]
  sheep_dir=[Var(:_2),Var(:_2)]; 
  sheep_eng=fill(:(round(Int, a/2, RoundUp)), 2); 
end

sheep_reprod_rule = Rule(hom(s_reprod_i,s_reprod_l),hom(s_reprod_i,s_reprod_r))
sheep_reprod = RuleSchedule("Sheep reproduce", sheep_reprod_rule)
wolf_reprod = RuleSchedule("Wolf reproduce", F(sheep_reprod_rule))

# Grass increment
#----------------
g_inc_l = @acset LV begin
  Grass=1; V=1; Eng=1; grass_loc=1; grass_eng=[Var(:a)]
end

g_inc_i = deepcopy(g_inc_l);
set_subpart!(g_inc_i, 1, :grass_eng, Var(:b))

g_inc_r = deepcopy(g_inc_i)
set_subpart!(g_inc_r, 1, :grass_eng, :(a-1))

g_inc_n = deepcopy(g_inc_l)
set_subpart!(g_inc_n,1, :grass_eng, 0)

g_inc = RuleSchedule("Grass increments",
  Rule(hom(g_inc_i, g_inc_l;bindvars=true), hom(g_inc_i, g_inc_r;bindvars=true),
      [NAC(hom(g_inc_l, g_inc_n; bindvars=true))]))


# Scheduling Rules
##################

# 25% chance of left turn, 25% chance of right turn, 50% stay in same direction
sheep_rotate = (NestedDWD(const_cond([1.,2.,1.]; name="sheep turn?")) 
                ⋅ (sheep_rotate_l ⊗ id(NPorts(1)) ⊗ sheep_rotate_r) 
                ⋅ merge_wires(3))
# likewise for wolves
wolf_rotate = (NestedDWD(const_cond([1.,2.,1.]; name="wolf turn?")) 
                ⋅ (wolf_rotate_l ⊗ id(NPorts(1)) ⊗ wolf_rotate_r) 
                ⋅ merge_wires(3))
# Sheep have 4% chance of reproducing, wolves have 5%
sheep_repro = (NestedDWD(const_cond([0.4, .96]; name="sheep reprod?")) 
              ⋅ (sheep_reprod ⊗ id(NPorts(1))) 
              ⋅ merge_wires(2))
wolf_repro = (NestedDWD(const_cond([0.5, .95]; name="wolf reprod?")) 
              ⋅ (wolf_reprod ⊗ id(NPorts(1))) 
              ⋅ merge_wires(2))
# Do all rules in a sequence
cycle = compose(sheep_rotate, wolf_rotate,
                sheep_move_forward, wolf_move_forward,
                sheep_eat, wolf_eat,
                sheep_starve, wolf_starve,
                sheep_repro,wolf_repro, g_inc) 

# wrap in a while loop
overall = WhileSchedule(cycle, curr -> nparts(curr,:Wolf) == 0) |> ocompose |> outer

G, coords = initialize(2, .25, .25)
pprint(Graph(G; positions=coords))
res = apply_schedule(overall, G; steps=20) # run 20 steps max

# Run these lines to view the trajectory
if false 
  using Interact
  using Blink: Window, body!
  w = Window()
  body!(w, view_traj(overall, res, Graph; positions=coords))
end
