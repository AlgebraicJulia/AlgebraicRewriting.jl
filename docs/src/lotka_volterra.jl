using Revise
using Catlab, Catlab.Theories, Catlab.CategoricalAlgebra
using Catlab.Graphs.BasicGraphs: TheoryGraph, HasGraph
using AlgebraicRewriting
using Random
using Test
const hom = AlgebraicRewriting.homomorphism
const rw = AlgebraicRewriting.rewrite
const rw_sch = AlgebraicRewriting.rewrite_schedule
const iso = AlgebraicRewriting.is_isomorphic
const R = AlgebraicRewriting.RuleSchedule
using Catlab.CategoricalAlgebra: is_natural



"""
Grass = 0 means alive grass, whereas grass > 0 represent a counter of time until
the grass is alive.

Sheeps and wolves have position and direction, so we assign each an *edge*. We
assume a convention where the location of the something is the edge SOURCE.

Dir is an attribute which can take values :N, :E, :W, and :S.
"""
@present TheoryLV <: TheoryGraph begin
  (Sheep,Wolf,Grass)::Ob
  (Dir, GrassVal,  Eng)::AttrType
  sheep_loc::Hom(Sheep, E)
  wolf_loc::Hom(Wolf, E)
  grass::Hom(Grass, V)
  grassval::Attr(Grass,GrassVal)
  dir::Attr(E, Dir)
  sheep_eng::Attr(Sheep, Eng)
  wolf_eng::Attr(Wolf, Eng)
end

@acset_type LV_Generic(TheoryLV) <: HasGraph
const LV = LV_Generic{Union{Var,Expr,Symbol}, Union{Var,Expr,Int}, Union{Var,Expr,Int}}

F = FinFunctor(
  Dict([:Sheep => :Wolf, :Wolf => :Sheep, :Grass => :Grass, :V=>:V, :E=>:E,
        :Dir=>:Dir, :GrassVal=>:GrassVal, :Eng=>:Eng]),
  Dict([:sheep_loc=>:wolf_loc, :wolf_loc=>:sheep_loc,
        :sheep_eng=>:wolf_eng, :wolf_eng=>:sheep_eng,
        :src=>:src,:tgt=>:tgt,:dir=>:dir,:grassval=>:grassval,:grass=>:grass]),
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
      coords[i=>j] = add_part!(lv, :V; grass=add_part!(
                      lv, :Grass; grassval=max(0,rand(-30:30))))
    end
  end
  for i in 0:n-1
    for j in 0:n-1
      add_part!(lv, :E; src=coords[i=>j], tgt=coords[mod(i+1,n)=>j], dir=:E)
      add_part!(lv, :E; src=coords[i=>j], tgt=coords[mod(i-1,n)=>j], dir=:W)
      add_part!(lv, :E; src=coords[i=>j], tgt=coords[i=>mod(j+1,n)], dir=:N)
      add_part!(lv, :E; src=coords[i=>j], tgt=coords[i=>mod(j-1,n)], dir=:S)
    end
  end
  c = fill(0=>0, nv(lv))
  for (k,v) in collect(coords) c[v] = k end
  return lv, c
end

function initialize(n::Int, sheep::Float64, wolves::Float64)
  grid, coords = create_grid(n)
  args = [(sheep, :Sheep, :sheep_loc, :sheep_eng), (wolves, :Wolf, :wolf_loc, :wolf_eng)]
  for (n_, name, loc, eng) in args
    for i in 1:round(Int,n_*n^2)
      add_part!(grid, name; Dict([eng=>5, loc=>rand(edges(grid))])...)
    end
  end
  return grid, coords
end

using Catlab.Graphics.Graphviz: Attributes, Statement, Node
using Catlab.Graphics.Graphviz

supscript_d = Dict(['1'=>'¹', '2'=>'²', '3'=>'³', '4'=>'⁴', '5'=>'⁵',
                    '6'=>'⁶', '7'=>'⁷', '8'=>'⁸', '9'=>'⁹', '0'=>'⁰'])
supscript(x::String) = join([get(supscript_d, c, c) for c in x])
function Graph(p::LV,positions; name="G", prog="neato", title="")
  pstr = ["$(i),$(j)!" for (i,j) in positions]
  stmts = Statement[]
    for s in 1:nv(p)
        vx, vy = positions[s]
        gv = p[only(incident(p, s, :grass)), :grassval]
        col = gv  == 0 ? "lightgreen" : "tan"
        push!(stmts,Node("v$s", Attributes(
                    :label=>gv == 0 ? "" : string(gv), #"v$s",
                    :shape=>"circle",
                    :color=> col, :pos=>pstr[s])))
    end
  d = Dict([:E=>(1,0),:N=>(0,1), :S=>(0,1),:W=>(-1,0),])
  for e in edges(p)
    s, t = src(p,e),tgt(p,e)
    dx, dy = d[p[e, :dir]]
    (sx,sy), (tx,ty) = positions[s], positions[t]

    for (is_wolf, loc, eng) in [(:true,:wolf_loc,:wolf_eng), (false, :sheep_loc, :sheep_eng)]
        for w in incident(p, e, loc)
            L, R = 0.25, 0.2
            wx = sx+L*dx+R*rand()
            wy = sy+L*dy+R*rand()
            ID = "$(is_wolf ? :w : :s)$w"
            append!(stmts,[Node(ID, Attributes(
                            :label=>"$w"*supscript("$(p[w,eng])"),
                            :shape=>"square", :width=>"0.3px", :height=>"0.3px", :fixedsize=>"true",
                            :pos=>"$(wx),$(wy)!",:color=> is_wolf ? "red" : "lightblue")),
                           ])

        end
    end
  end


  g = Graphviz.Digraph(name, Statement[stmts...]; prog=prog,
        graph_attrs=Attributes(:label=>title, :labelloc=>"t"),
        node_attrs=Attributes(:shape=>"plain", :style=>"filled"))
  return g
end


# RULES
#######
seq = Schedule[]

# Rotating
#---------
function shift(dirs::Vector{Pair{Symbol,Symbol}}, n::Symbol)
  ListSchedule(Vector{Schedule}(map(dirs) do (d1, d2)
  l = @acset LV begin
    Sheep=1; V=3; E=2
    src=1; tgt=[2,3]
    sheep_eng=[Var(:x)]; dir=Symbol[d1,d2];
    sheep_loc=1
  end

  i = deepcopy(l); rem_part!(i, :Sheep, 1)

  r = deepcopy(i)
  add_part!(r, :Sheep; sheep_eng=Var(:x), sheep_loc=2)

  RuleSchedule(Rule(hom(i,l), hom(i,r)), Symbol("sheep-$d1-$d2"))
            end), n)
end

sheep_rotate_l =  shift([:N=>:W,:W=>:S,:S=>:E,:E=>:N],:sheep_rotate_l)
sheep_rotate_r =  shift([:N=>:E,:W=>:N,:S=>:W,:E=>:S],:sheep_rotate_r)
wolf_rotate_l = rename_schedule(F(sheep_rotate_l),:wolf_rotate_l)
wolf_rotate_r = rename_schedule(F(sheep_rotate_r),:wolf_rotate_r)

append!(seq, [sheep_rotate_l,sheep_rotate_r,
              wolf_rotate_l,wolf_rotate_r]);

# Moving forward
#---------------
s_move_forward_l = @acset LV begin
  Sheep=1; V=3; E=2;
  src=[1,2]; tgt=[2,3]; dir=[Var(:a), Var(:a)]
  sheep_eng=[Var(:x)]; sheep_loc=1
end

s_move_forward_i = deepcopy(s_move_forward_l)
rem_part!(s_move_forward_i, :Sheep, 1)

s_move_forward_r = deepcopy(s_move_forward_i)
add_part!(s_move_forward_r, :Sheep; sheep_loc=2, sheep_eng=:(x-1))

sheep_move_forward = Rule(hom(s_move_forward_i, s_move_forward_l),
                          hom(s_move_forward_i, s_move_forward_r))

wolf_move_forward = F(sheep_move_forward)

append!(seq, [R(sheep_move_forward,:sheep_move_forward),
              R(wolf_move_forward, :wolf_move_forward)]);
# Eat grass + 4eng
#-----------------
s_eat_l = @acset LV begin
  Sheep=1; Grass=1; V=2; E=1;
  src=1;tgt=2; dir=[Var(:d)];
  sheep_eng=[Var(:e)]; sheep_loc=1
  grass=1; grassval=0
end
s_eat_i = deepcopy(s_eat_l)
rem_part!(s_eat_i, :Sheep, 1); rem_part!(s_eat_i, :Grass, 1)

s_eat_r = deepcopy(s_eat_i)
add_part!(s_eat_r, :Sheep; sheep_eng=:(e+4), sheep_loc=1)
add_part!(s_eat_r, :Grass; grassval=30, grass=1)

sheep_eat = Rule(hom(s_eat_i, s_eat_l), hom(s_eat_i, s_eat_r))

push!(seq, R(sheep_eat,:sheep_eat));

# Eat sheep + 20 eng
#-------------------
w_eat_l = @acset LV begin
  Sheep=1; Wolf=1; V=2; E=1;
  src=1;tgt=2; dir=[Var(:d)];
  sheep_eng=[Var(:e)]; sheep_loc=1
  wolf_eng=[Var(:w)]; wolf_loc=1
end

w_eat_i = deepcopy(w_eat_l)
rem_part!(w_eat_i, :Sheep, 1); rem_part!(w_eat_i, :Wolf, 1)

w_eat_r = deepcopy(w_eat_i)
add_part!(w_eat_r, :Wolf; wolf_eng=:(w+20), wolf_loc=1)

wolf_eat = Rule(hom(w_eat_i, w_eat_l), hom(w_eat_i, w_eat_r))

push!(seq, R(wolf_eat,:wolf_eat));

# Die if 0 eng
#-------------
s_die_l = @acset LV begin
  Sheep=1; V=2; E=1; src=1;tgt=2; dir=[Var(:d)];
  sheep_eng=[0]; sheep_loc=1
end

s_die_r = deepcopy(s_die_l); rem_part!(s_die_r, :Sheep, 1)

sheep_die = Rule(hom(s_die_r, s_die_l), id(s_die_r))
wolf_die = F(sheep_die)
append!(seq, [R(sheep_die,:sheep_die),R(wolf_die,:wolf_die)]);

# reproduce (4% sheep, 5% wolf)
#------------------------------
s_reprod_l =  @acset LV begin
  Sheep=1; V=2; E=1; src=1;tgt=2; dir=[Var(:d)];
  sheep_eng=[Var(:a)]; sheep_loc=1
end

s_reprod_i = deepcopy(s_reprod_l); rem_part!(s_reprod_i, :Sheep, 1)

s_reprod_r = deepcopy(s_reprod_i)
add_parts!(s_reprod_r, :Sheep, 2; sheep_loc=[1,1],
           sheep_eng=[:(round(Int, a/2, RoundUp))])

sheep_reprod = Rule(hom(s_reprod_i,s_reprod_l),hom(s_reprod_i,s_reprod_r))
wolf_reprod = F(sheep_reprod)

append!(seq, [R(sheep_reprod,:sheep_reprod),
              R(wolf_reprod, :wolf_reprod)]);

# Grass increment
#----------------
g_inc_l = @acset LV begin
  Grass=1; V=1; grassval=[Var(:a)]; grass=1
end

g_inc_i = deepcopy(g_inc_l); rem_part!(g_inc_i, :Grass, 1);

g_inc_r = deepcopy(g_inc_i)
add_part!(g_inc_r, :Grass; grassval=:(max(0, a-1)), grass=1)

g_inc = Rule(hom(g_inc_i, g_inc_l), hom(g_inc_i, g_inc_r))

push!(seq, R(g_inc,:g_inc));
# overall
#--------
step = ListSchedule(seq)
only_sheep(prev, curr) = nparts(curr,:Wolf) == 0
overall = WhileSchedule(step, :main, only_sheep);


G, coords = initialize(2, .25, .25)
res = apply_schedule(step, G=G, verbose=false)
view(res; viewer=Graph, positions=coords)