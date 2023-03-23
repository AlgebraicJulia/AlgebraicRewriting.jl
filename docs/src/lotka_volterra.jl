module LotkaVolterra 

using Catlab, Catlab.Theories, Catlab.CategoricalAlgebra, Catlab.Graphs, 
      Catlab.Graphics, Catlab.WiringDiagrams
using AlgebraicRewriting
using Random, Test, StructEquality

Random.seed!(123);

using Catlab.Graphics.Graphviz: Attributes, Statement, Node
using Catlab.Graphics.Graphviz

import Catlab.CategoricalAlgebra: left, right

abstract type Direction end 
begin
  @struct_hash_equal struct North <: Direction end 
  @struct_hash_equal struct South <: Direction end 
  @struct_hash_equal struct East <: Direction end 
  @struct_hash_equal struct West <: Direction end 
  show(io,::North) = show(io, :N); show(io,::South) = show(io, :S)
  show(io,::East) = show(io, :E); show(io,::West) = show(io, :W)
  right(::North) = East(); right(::East) = South(); 
  right(::South) = West(); right(::West) = North()
  left(::North) = West(); left(::East) = North()
  left(::South) = East(); left(::West) = South()
  NEWS = Dict(North()=>"N",East()=>"E",West()=>"W",South()=>"S")
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

@present TheoryLV′ <: TheoryLV begin
  Coord::AttrType 
  coord::Attr(V,Coord)
end



to_graphviz(TheoryLV; prog="dot")

@acset_type LV_Generic(TheoryLV) <: HasGraph
const LV = LV_Generic{Direction, Int}

@acset_type LV′_Generic(TheoryLV′) <: HasGraph
const LV′ = LV′_Generic{Direction, Int, Tuple{Int,Int}}

F = Migrate(
  Dict(:Sheep=>:Wolf, :Wolf=>:Sheep), 
  Dict([:sheep_loc=>:wolf_loc, :wolf_loc=>:sheep_loc,
        :sheep_eng=>:wolf_eng, :wolf_eng=>:sheep_eng,:grass_eng =>:grass_eng,
        :sheep_dir=>:wolf_dir, :wolf_dir=>:sheep_dir,]), LV)
F2 = Migrate(
  Dict(x=>x for x in Symbol.(TheoryLV.generators[:Ob])), 
  Dict(x=>x for x in Symbol.(TheoryLV.generators[:Hom])), LV′; delta=false)

"""
Create a nxn grid with periodic boundary conditions. Edges in each cardinal
direction originate at every point


(i,j+1) -> (i+1,j+1) -> ...
  ↑          ↑
(i,j)   -> (i+1,j)   -> ...

"""
function create_grid(n::Int)
  lv = LV′()
  coords = Dict()
  # Initialize grass 50% green, 50% uniformly between 0-30
  for i in 0:n-1
    for j in 0:n-1
      coords[i=>j] = add_part!(lv, :V; grass_eng=max(0,rand(-30:30)), coord=(i,j))
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
  return lv
end

g = create_grid(2)


"""
`n` is the length of the grid.
`sheep` and `wolves` are the fraction of spaces that are 
populated with that animal
"""
function initialize(n::Int, sheep::Float64, wolves::Float64)::LV′
  grid = create_grid(n)
  args = [(sheep, :Sheep, :sheep_loc, :sheep_eng, :sheep_dir),
          (wolves, :Wolf, :wolf_loc, :wolf_eng, :wolf_dir)]
  for (n_, name, loc, eng, d) in args
    for _ in 1:round(Int,n_*n^2)
      dic = Dict([eng => 5, loc => rand(vertices(grid)),
                  d => rand([North(),East(),South(),West()])])
      add_part!(grid, name; dic...)
    end
  end
  return grid
end


supscript_d = Dict([
  '1'=>'¹', '2'=>'²', '3'=>'³', '4'=>'⁴', '5'=>'⁵','6'=>'⁶', '7'=>'⁷', '8'=>'⁸', 
  '9'=>'⁹', '0'=>'⁰', 'x'=>'ˣ', 'y'=>'ʸ','z'=>'ᶻ','a'=>'ᵃ','b'=>'ᵇ','c'=>'ᶜ',
  'd'=>'ᵈ'])
supscript(x::String) = join([get(supscript_d, c, c) for c in x])

"""Visualize a LV"""
function view_LV(p::ACSetTransformation; name="G", title="")
  if nparts(dom(p),:Wolf) == 1 
    star = :Wolf=>p[:Wolf](1)
  elseif nparts(dom(p),:Sheep) == 1 
    star = :Sheep=>p[:Sheep](1)
  elseif nparts(dom(p),:V) == 1 
    star = :V=>p[:V](1)
  else
    star = nothing
  end
  view_LV(codom(p); name=name, title=title, star=star)
end  
function view_LV(p::LV′; name="G", title="", star=nothing)
  pstr = ["$(i),$(j)!" for (i,j) in p[:coord]]
  stmts = Statement[]
    for s in 1:nv(p)
      st = (star == (:V=>s)) ? "*" : ""
      gv = p[s, :grass_eng]
      col = gv  == 0 ? "lightgreen" : "tan"
      push!(stmts,Node("v$s", Attributes(
                  :label=>gv == 0 ? "" : string(gv)*st,
                  :shape=>"circle",
                  :color=> col, :pos=>pstr[s])))
    end
  d = Dict([East()=>(1,0),North()=>(0,1), South()=>(0,-1),West()=>(-1,0),])

  args = [(:true,:Wolf,:wolf_loc,:wolf_eng,:wolf_dir),
          (false, :Sheep, :sheep_loc, :sheep_eng,:sheep_dir)]

  for (is_wolf, prt, loc, eng, dr) in args
    for w in parts(p, prt)
      st = (star == ((is_wolf ? :Wolf : :Sheep) => w)) ? "*" : ""
      e = only(incident(p,p[w,loc], :src) ∩ incident(p,p[w,dr], :dir))
      s = src(p,e)
      dx, dy = d[p[e, :dir]]
      (sx,sy) = p[s,:coord]

      L, R = 0.25, 0.1
      wx = sx+L*dx+R*rand()
      wy = sy+L*dy+R*rand()
      ID = "$(is_wolf ? :w : :s)$w"
      append!(stmts,[Node(ID, Attributes(
        :label=>"$w"*supscript("$(p[w,eng])")*st,
        :shape=>"square", :width=>"0.3px", :height=>"0.3px", :fixedsize=>"true",
        :pos=>"$(wx),$(wy)!",:color=> is_wolf ? "red" : "lightblue"))])
    end
  end

  g = Graphviz.Digraph(name, Statement[stmts...]; prog="neato",
        graph_attrs=Attributes(:label=>title, :labelloc=>"t"),
        node_attrs=Attributes(:shape=>"plain", :style=>"filled"))
  return g
end

i1 = initialize(2,.5,.5)
view_LV(i1)

# RULES
#######
# Empty agent type
I = LV()
# Generic sheep agent
S = @acset LV begin
  Sheep=1; V=1; Dir=1; Eng=2; sheep_loc=1; grass_eng=[AttrVar(1)]
  sheep_dir=[AttrVar(1)]; sheep_eng=[AttrVar(2)]; 
end
# Generic wolf agent
W = F(S)
# Generic grass agent
G = @acset LV begin V=1; Eng=1; grass_eng=[AttrVar(1)] end

N = Dict(W=>"W",S=>"S",G=>"G", I=>"")
# Rotating
#---------

rl = Rule(id(S),id(S); expr=(Dir=[xs->left(only(xs))],))
rr = Rule(id(S),id(S); expr=(Dir=[xs->right(only(xs))],))

sheep_rotate_l = tryrule(RuleApp(:turn_left, rl, S))
sheep_rotate_r = tryrule(RuleApp(:turn_right, rr, S))

# we can imagine executing these rules in sequence or in parallel
sched = (sheep_rotate_l⋅sheep_rotate_r) 
view_sched(sched; names=N)


# Moving forward
#---------------
s_fwd_l = @acset LV begin
  Sheep=1; V=2; E=1; sheep_loc=1; Dir=1; Eng=3
  src=1; tgt=2; dir=[AttrVar(1)]; 
  grass_eng=AttrVar.(1:2)
  sheep_dir=[AttrVar(1)]; sheep_eng=[AttrVar(3)]
end

s_fwd_i = deepcopy(s_fwd_l)
rem_part!(s_fwd_i, :Sheep, 1); 
rem_part!(s_fwd_i, :Eng, 3)

s_fwd_r = deepcopy(s_fwd_l)
s_fwd_r[1, :sheep_loc] = 2

s_n = deepcopy(s_fwd_l)
set_subpart!(s_n, 1, :sheep_eng, 0); 
rem_part!(s_n, :Eng, 3)

sheep_fwd_rule = Rule(
  homomorphism(s_fwd_i, s_fwd_l; monic=true),
  homomorphism(s_fwd_i, s_fwd_r; monic=true),
  ac=[AppCond(homomorphism(s_fwd_l, s_n), false)],
  expr=(Eng=[vs->vs[1], vs->vs[2], vs->vs[3]-1],)
)

sheep_fwd = tryrule(RuleApp(:move_fwd, sheep_fwd_rule, 
  homomorphism(S,s_fwd_l), homomorphism(S,s_fwd_r)))

begin # test 
  ex = @acset LV begin Sheep=1; V=3; E=2; src=[1,2]; tgt=[2,3]; sheep_loc=2
    sheep_eng=[3]; grass_eng=[9,10,11]; dir=fill(North(),2); sheep_dir=[North()]
  end
  expected = deepcopy(ex); 
  expected[1,:sheep_loc] = 3; 
  expected[1,:sheep_eng] = 2
  @test is_isomorphic(expected, rewrite(sheep_fwd_rule,ex))
end

# Eat grass + 4eng
#-----------------
# Grass is at 0 - meaning it's ready to be eaten
s_eat_l = @acset LV begin
  Sheep=1; Eng=1; Dir=1; V=1; sheep_loc=1;  grass_loc=1; 
  grass_eng=[0]; sheep_eng=[AttrVar(1)]; sheep_dir=[AttrVar(1)]
end

se_rule = Rule(homomorphism(S,s_eat_l), id(S); expr=(Eng=[vs->30,vs->only(vs)+4],))
sheep_eat = tryrule(RuleApp(:Sheep_eat, se_rule, S))

begin # test 
  ex = @acset LV begin Sheep=1; V=3; E=2; src=[1,2]; tgt=[2,3]; sheep_loc=2
    sheep_eng=[3]; grass_eng=[9,0,11]; dir=fill(North(),2); sheep_dir=[North()]
  end

  rewrite(se_rule,ex)
end 

# Eat sheep + 20 eng
#-------------------

w_eat_l = @acset LV begin
  Sheep=1; Wolf=1; V=1; Eng=3; Dir=2; grass_eng=[AttrVar(1)]
  sheep_dir=[AttrVar(1)]; wolf_dir=[AttrVar(2)]; 
  sheep_eng=[AttrVar(2)]; wolf_eng=[AttrVar(3)]
  sheep_loc=1; wolf_loc=1
end

w_eat_r = @acset LV begin
  Wolf=1; V=1; Eng=2; Dir=1; grass_eng=[AttrVar(1)]
  wolf_dir=[AttrVar(1)]; wolf_eng=[AttrVar(2)]; wolf_loc=1
end

we_rule = Rule(homomorphism(w_eat_r, w_eat_l), id(w_eat_r); expr=(Eng=[vs->vs[1],vs->vs[3]+20],))
wolf_eat = tryrule(RuleApp(:Wolf_eat, we_rule, W))

begin # test 
  ex = @acset LV begin Sheep=1; Wolf=1; V=3; E=2; src=[1,2]; tgt=[2,3]; sheep_loc=2
    sheep_eng=[3]; grass_eng=[9,10,11]; dir=fill(North(),2); sheep_dir=[North()]
    wolf_loc=[2]; wolf_eng=[16]; wolf_dir=[South()]
  end
  expected = @acset LV begin Wolf=1; V=3; E=2; src=[1,2]; tgt=[2,3]; 
    grass_eng=[9,10,11]; dir=fill(North(),2); sheep_dir=[North()]
    wolf_loc=[2]; wolf_eng=[36]; wolf_dir=[South()]
  end
  @test is_isomorphic(rewrite(we_rule,ex), expected)
end

# Die if 0 eng
#-------------
s_die_l = @acset LV begin
  Sheep=1; V=1; Eng=1; Dir=1; grass_eng=[AttrVar(1)]
  sheep_eng=[0]; sheep_loc=1; sheep_dir=[AttrVar(1)]
end
sheep_die_rule = Rule(homomorphism(G, s_die_l), id(G))
sheep_starve = (RuleApp(:starve, sheep_die_rule, 
                       homomorphism(S,s_die_l), create(G))
                ⋅ (id([I]) ⊗ Weaken(create(S))) ⋅ merge_wires(I))

# view_sched(sheep_starve |> typecheck)

begin # test 
  ex = @acset LV begin Sheep=1; Wolf=1; V=3; E=2; src=[1,2]; tgt=[2,3]; sheep_loc=2
    sheep_eng=[0]; grass_eng=[9,10,11]; dir=fill(North(),2); sheep_dir=[North()]
    wolf_loc=[2]; wolf_eng=[16]; wolf_dir=[South()]
  end
  expected = @acset LV begin Wolf=1; V=3; E=2; src=[1,2]; tgt=[2,3]; 
    grass_eng=[9,10,11]; dir=fill(North(),2);
    wolf_loc=[2]; wolf_eng=[16]; wolf_dir=[South()]
  end
  @test is_isomorphic(rewrite(sheep_die_rule,ex), expected)
end

# reproduction
#-------------

s_reprod_r =  @acset LV begin
  Sheep=2; V=1; Eng=3; Dir=2; sheep_loc=1; grass_eng=[AttrVar(1)]
  sheep_dir=AttrVar.(1:2); sheep_eng=AttrVar.(2:3); 
end

sheep_reprod_rule = Rule(
  homomorphism(G, S),
  homomorphism(G, s_reprod_r); 
  expr=(Dir=[vs->vs[1],vs->vs[1]], Eng=[vs->vs[1], 
             fill(vs->round(Int, vs[2]/2, RoundUp), 2)...],)
  )

sheep_reprod = RuleApp(:reproduce, sheep_reprod_rule, 
                       id(S), homomorphism(S, s_reprod_r)) |> tryrule

begin # test 
  ex = @acset LV begin Sheep=1; Wolf=1; V=3; E=2; src=[1,2]; tgt=[2,3]; sheep_loc=2
    sheep_eng=[10]; grass_eng=[9,10,11]; dir=fill(North(),2); sheep_dir=[North()]
    wolf_loc=[2]; wolf_eng=[16]; wolf_dir=[South()]
  end
  expected = @acset LV begin Sheep=2; Wolf=1; V=3; E=2; src=[1,2]; tgt=[2,3]; sheep_loc=2
    sheep_eng=[5,5]; grass_eng=[9,10,11]; dir=fill(North(),2); sheep_dir=[North(),North()]
    wolf_loc=[2]; wolf_eng=[16]; wolf_dir=[South()]
  end
  @test is_isomorphic(rewrite(sheep_reprod_rule,ex),expected)
end

# Grass increment
#----------------

g_inc_n = deepcopy(G)
set_subpart!(g_inc_n,1, :grass_eng, 0); 
rem_part!(g_inc_n, :Eng, 1)

g_inc_rule = Rule(id(G), id(G);
                  ac=[AppCond(homomorphism(G, g_inc_n), false)],
                  expr=(Eng=[vs->only(vs)-1],))
g_inc = RuleApp(:GrassIncrements,g_inc_rule, G) |> tryrule


begin # test 
  ex = @acset LV begin Sheep=1; V=3; E=2; src=[1,2]; tgt=[2,3]; sheep_loc=2
    sheep_eng=[3]; grass_eng=[1,10,2]; dir=fill(North(),2); sheep_dir=[North()]
  end
  expected = @acset LV begin Sheep=1; V=3; E=2; src=[1,2]; tgt=[2,3]; sheep_loc=2
    sheep_eng=[3]; grass_eng=[0,10,2]; dir=fill(North(),2); sheep_dir=[North()]
  end
  @test is_isomorphic(rewrite(g_inc_rule,ex), expected)
end

# Scheduling Rules
##################

# Stuff that happens once per sheep 
#----------------------------------

# 25% chance of left turn, 25% chance of right turn, 50% stay in same direction
general = mk_sched(NamedTuple(),(init=:S,), (
  S = S, I = I, G = G,
  turn   = const_cond([1.,2.,1.], S; name=:turn), 
  maybe  = const_cond([0.1, 0.9], S; name=:reprod), 
  lft    = sheep_rotate_l, 
  rght   = sheep_rotate_r, 
  fwd    = sheep_fwd, 
  repro  = sheep_reprod, 
  starve = sheep_starve), 
  quote 
    out_l, out_str, out_r = turn(init)
    moved = fwd([lft(out_l), out_str, rght(out_r)]) 
    out_repro, out_no_repro = maybe(moved)
    return starve([repro(out_repro), out_no_repro])
end)

sheep = sheep_eat ⋅ general   # once per sheep
wolf = wolf_eat ⋅ F(general)  # once per wolf

# Do all sheep, then all wolves, then all daily operations
cycle = ( agent(sheep, S; n=:sheep,  ret=I)
        ⋅ agent(wolf,  W; n=:wolves, ret=I)
        ⋅ agent(g_inc, G; n=:grass))

# wrap in a while loop
overall = while_schedule(cycle, curr -> nparts(curr,:Wolf) >= 0) |> F2
view_sched(overall; names=F2(N))
X = initialize(3, .25, .25)
res = apply_schedule(overall, X; steps=50, verbose=false);

# Run these lines to view the trajectory
using Luxor
view_traj(overall, res, view_LV; agent=true)

end # module
