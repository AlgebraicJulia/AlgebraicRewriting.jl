using Catlab, Catlab.Theories, Catlab.CategoricalAlgebra, Catlab.Graphs
using AlgebraicRewriting
using Random
using Test
const hom = AlgebraicRewriting.homomorphism
const R = AlgebraicRewriting.RuleSchedule

using Catlab.Graphics.Graphviz: Attributes, Statement, Node
using Catlab.Graphics.Graphviz


"""
Grass = 0 means alive grass, whereas grass > 0 represent a counter of time until
the grass is alive.

Sheeps and wolves have position and direction, so we assign each an *edge*. We
assume a convention where the location of the something is the edge SOURCE.

Dir is an attribute which can take values :N, :E, :W, and :S.
"""
@present TheoryLV <: SchGraph begin
  (Sheep,Wolf,Grass,Dir,Eng)::Ob
  (DirVal,EngVal)::AttrType
  grass_eng::Hom(Grass, Eng)
  sheep_eng::Hom(Sheep, Eng)
  wolf_eng::Hom(Wolf, Eng)
  grass_loc::Hom(Grass, V)
  sheep_loc::Hom(Sheep, V)
  wolf_loc::Hom(Wolf, V)
  sheep_dir::Hom(Sheep, Dir)
  wolf_dir::Hom(Wolf, Dir)
  dir::Hom(E, Dir)
  eval::Attr(Eng,EngVal)
  dval::Attr(Dir,DirVal)
end

@acset_type LV_Generic(TheoryLV) <: HasGraph
const LV = LV_Generic{Union{Var,Expr,Symbol}, Union{Var,Expr,Int}}

F = FinFunctor(
  Dict([:Sheep => :Wolf, :Wolf => :Sheep, :V=>:V, :E=>:E, :Grass=>:Grass,
        :Dir=>:Dir,:DirVal=>:DirVal, :Eng=>:Eng,:EngVal=>:EngVal]),
  Dict([:sheep_loc=>:wolf_loc, :wolf_loc=>:sheep_loc,:grass_loc =>:grass_loc,
        :sheep_eng=>:wolf_eng, :wolf_eng=>:sheep_eng,:grass_eng =>:grass_eng,
        :sheep_dir=>:wolf_dir, :wolf_dir=>:sheep_dir,
        :src=>:src,:tgt=>:tgt,:dir=>:dir,
        :eval=>:eval,:dval=>:dval]),
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
  add_parts!(lv, :Dir, 4; dval=[:N,:E,:S,:W])
  coords = Dict()
  # Initialize grass 50% green, 50% uniformly between 0-30
  for i in 0:n-1
    for j in 0:n-1
      coords[i=>j] = add_part!(lv, :V);
      add_part!(lv,:Grass; grass_loc=coords[i=>j], grass_eng=add_part!(
            lv, :Eng; eval=max(0,rand(-30:30))))

    end
  end
  for i in 0:n-1
    for j in 0:n-1
      add_part!(lv, :E; src=coords[i=>j], tgt=coords[mod(i+1,n)=>j], dir=2)
      add_part!(lv, :E; src=coords[i=>j], tgt=coords[mod(i-1,n)=>j], dir=4)
      add_part!(lv, :E; src=coords[i=>j], tgt=coords[i=>mod(j+1,n)], dir=1)
      add_part!(lv, :E; src=coords[i=>j], tgt=coords[i=>mod(j-1,n)], dir=3)
    end
  end
  c = fill(0=>0, nv(lv))
  for (k,v) in collect(coords) c[v] = k end
  return lv, c
end

function initialize(n::Int, sheep::Float64, wolves::Float64)
  grid, coords = create_grid(n)
  args = [(sheep, :Sheep, :sheep_loc, :sheep_eng, :sheep_dir),
          (wolves, :Wolf, :wolf_loc, :wolf_eng, :wolf_dir)]
  for (n_, name, loc, eng, d) in args
    for i in 1:round(Int,n_*n^2)
      dic = Dict([eng=>add_part!(grid, :Eng; eval=5), loc=>rand(vertices(grid)),
                  d=>rand(1:4)])
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
function Graph(p::LV,positions; name="G", prog="neato", title="")
  pstr = ["$(i),$(j)!" for (i,j) in positions]
  stmts = Statement[]
    for s in 1:nv(p)
        vx, vy = positions[s]
        g= only(incident(p, s, :grass_loc))
        gv = p[g, [:grass_eng,:eval]]
        col = gv  == 0 ? "lightgreen" : "tan"
        push!(stmts,Node("v$s", Attributes(
                    :label=>gv == 0 ? "" : string(gv), #"v$s",
                    :shape=>"circle",
                    :color=> col, :pos=>pstr[s])))
    end
  d = Dict([:E=>(1,0),:N=>(0,1), :S=>(0,1),:W=>(-1,0),])

  args = [(:true,:Wolf,:wolf_loc,:wolf_eng,:wolf_dir),
          (false, :Sheep, :sheep_loc, :sheep_eng,:sheep_dir)]

  for (is_wolf, prt, loc, eng, dr) in args
    for w in parts(p, prt)
      e = only(incident(p,p[w,loc], :src) ∩ incident(p,p[w,dr], :dir))
      s, t = src(p,e),tgt(p,e)
      dx, dy = d[p[e, [:dir,:dval]]]
      (sx,sy), (tx,ty) = positions[s], positions[t]

      L, R = 0.25, 0.1
      wx = sx+L*dx+R*rand()
      wy = sy+L*dy+R*rand()
      ID = "$(is_wolf ? :w : :s)$w"
      append!(stmts,[Node(ID, Attributes(
        :label=>"$w"*supscript("$(p[w,[eng,:eval]])"),
        :shape=>"square", :width=>"0.3px", :height=>"0.3px", :fixedsize=>"true",
        :pos=>"$(wx),$(wy)!",:color=> is_wolf ? "red" : "lightblue")),
        ])

    end
  end


  g = Graphviz.Digraph(name, Statement[stmts...]; prog=prog,
        graph_attrs=Attributes(:label=>title, :labelloc=>"t"),
        node_attrs=Attributes(:shape=>"plain", :style=>"filled"))
  return g
end

i1,i2=initialize(2,0.5,0.5)
i1
Graph(i1,i2)


# RULES
#######
seq = Schedule[]

# Rotating
#---------
function shift(lft::Bool=true)
  lexpr = :(Dict(:N=>:W,:W=>:S,:S=>:E,:E=>:N)[d])
  rexpr = :(Dict(:N=>:E,:E=>:S,:S=>:W,:W=>:N)[d])
  l = @acset LV begin
    Sheep=1; V=1; Dir=2; Eng=1;
    sheep_eng=1; sheep_dir=1; sheep_loc=1
    dval=[Var(:d), lft ? lexpr : rexpr];
    eval=[Var(:x)]
  end


  i = deepcopy(l); rem_part!(i, :Sheep, 1)

  r = deepcopy(i)
  add_part!(r, :Sheep; sheep_dir=2, sheep_eng=1, sheep_loc=1)

  Rule(hom(i,l;monic=true), hom(i,r;monic=true))

end

sheep_rotate_l = R(shift(),         :sheep_left,  false, 0.5)
sheep_rotate_r = R(shift(false),    :sheep_right, false, 0.5)
wolf_rotate_l  = R(F(shift()),      :wolf_left,   false, 0.5)
wolf_rotate_r  = R(F(shift(false)), :wolf_left,   false, 0.5)

append!(seq, [sheep_rotate_l,sheep_rotate_r,
              wolf_rotate_l,wolf_rotate_r]);

# Moving forward
#---------------
s_move_forward_l = @acset LV begin
  Sheep=1; V=2; E=1;Dir=1; Eng=1
  src=1; tgt=2;dir=1; sheep_dir=1; sheep_eng=1
  eval=[Var(:x)]; sheep_loc=1; dval=[Var(:z)]
end


s_move_forward_i = deepcopy(s_move_forward_l)
rem_part!(s_move_forward_i, :Sheep, 1); rem_part!(s_move_forward_i, :Eng, 1)

s_move_forward_r = deepcopy(s_move_forward_i)
e = add_part!(s_move_forward_r, :Eng, eval=:(x-1))
add_part!(s_move_forward_r, :Sheep; sheep_loc=2, sheep_eng=e, sheep_dir=1)

s_move_n = deepcopy(s_move_forward_l)
set_subpart!(s_move_n, 1, :eval, 0)

sheep_move_forward = Rule(
  hom(s_move_forward_i, s_move_forward_l; monic=true),
  hom(s_move_forward_i, s_move_forward_r; monic=true),
  [NAC(hom(s_move_forward_l, s_move_n; monic=true,bindvars=true))]
)

wolf_move_forward = F(sheep_move_forward)

append!(seq, [R(sheep_move_forward,:sheep_move_forward),
              R(wolf_move_forward, :wolf_move_forward)]);

# Eat grass + 4eng
#-----------------
s_eat_l = @acset LV begin
  Sheep=1; Eng=2; V=1; Dir=1; Grass=1
  sheep_loc=1;  grass_eng=1; sheep_eng=2; sheep_dir=1
  grass_loc=1; dval=[Var(:d)]; eval=[0, Var(:e)];
end

s_eat_i = deepcopy(s_eat_l)
rem_part!(s_eat_i, :Sheep, 1); rem_part!(s_eat_i, :Grass, 1)
rem_parts!(s_eat_i, :Eng, 1:2)

s_eat_r = deepcopy(s_eat_i)
add_parts!(s_eat_r, :Eng, 2; eval=[:(e+4),30])
add_part!(s_eat_r, :Sheep; sheep_eng=1, sheep_loc=1,sheep_dir=1)
add_part!(s_eat_r, :Grass; grass_loc=1, grass_eng=2)

sheep_eat = Rule(hom(s_eat_i, s_eat_l), hom(s_eat_i, s_eat_r))

push!(seq, R(sheep_eat,:sheep_eat));

# Eat sheep + 20 eng
#-------------------
w_eat_l = @acset LV begin
  Sheep=1; Wolf=1; V=1; Eng=2; Dir=2
  sheep_dir=1; wolf_dir=2; sheep_eng=1; wolf_eng=2
  sheep_loc=1; wolf_loc=1
  dval=[Var(:x),Var(:y)]; eval=[Var(:a),Var(:b)];
end

w_eat_i = deepcopy(w_eat_l)
rem_part!(w_eat_i, :Sheep, 1); rem_part!(w_eat_i, :Wolf, 1)
rem_parts!(w_eat_i, :Eng, 1:2)
rem_part!(w_eat_i, :Dir, 1)

w_eat_r = deepcopy(w_eat_i)
add_part!(w_eat_r, :Wolf; wolf_eng=add_part!(w_eat_r,:Eng, eval=:(b+20)),
          wolf_dir=1, wolf_loc=1)

wolf_eat = Rule(hom(w_eat_i, w_eat_l), hom(w_eat_i, w_eat_r))

push!(seq, R(wolf_eat,:wolf_eat));

# Die if 0 eng
#-------------
s_die_l = @acset LV begin
  Sheep=1; V=2; Eng=1; Dir=1; dir=1; dval=[Var(:d)];
  sheep_eng=1; eval=[0]; sheep_loc=1; sheep_dir=1
end

s_die_r = deepcopy(s_die_l);
[rem_part!(s_die_r, x, 1) for x in [:Sheep, :Eng, :Dir]
]
sheep_die = Rule(hom(s_die_r, s_die_l), id(s_die_r))
wolf_die = F(sheep_die)
append!(seq, [R(sheep_die,:sheep_die),R(wolf_die,:wolf_die)]);

# reproduce (4% sheep, 5% wolf)
#------------------------------
s_reprod_l =  @acset LV begin
  Sheep=1; V=1; Dir=1; Eng=1; sheep_dir=1; dval=[Var(:d)];
  sheep_eng=1; eval=[Var(:a)]; sheep_loc=1
end

s_reprod_i = deepcopy(s_reprod_l);
[rem_part!(s_reprod_i,x, 1) for x in [:Sheep, :Eng]]

s_reprod_r = deepcopy(s_reprod_i)
add_parts!(s_reprod_r, :Eng, 2; eval=fill(:(round(Int, a/2, RoundUp)), 2))
add_part!(s_reprod_r, :Dir; dval=Var(:d))
add_parts!(s_reprod_r, :Sheep, 2; sheep_loc=1, sheep_dir=[1,2], sheep_eng=[1,2])

sheep_reprod = Rule(hom(s_reprod_i,s_reprod_l),hom(s_reprod_i,s_reprod_r))

wolf_reprod = F(sheep_reprod)

append!(seq, [R(sheep_reprod,:sheep_reprod, false, 0.04),
              R(wolf_reprod, :wolf_reprod, false, 0.05)]);

# Grass increment
#----------------
g_inc_l = @acset LV begin
  Grass=1; V=1; Eng=1; grass_loc=1; grass_eng=1; eval=[Var(:a)]
end

g_inc_i = deepcopy(g_inc_l);
[rem_part!(g_inc_i, x, 1) for x in [:Grass, :Eng]]

g_inc_r = deepcopy(g_inc_i)
add_part!(g_inc_r, :Grass;
          grass_eng=add_part!(g_inc_r,:Eng; eval=:(a-1)), grass_loc=1)

g_inc_n = deepcopy(g_inc_l)
set_subpart!(g_inc_n, :eval, 0)

g_inc = Rule(hom(g_inc_i, g_inc_l), hom(g_inc_i, g_inc_r),
             [NAC(hom(g_inc_l, g_inc_n; bindvars=true))])

push!(seq, R(g_inc,:g_inc));
# overall
#--------
step = ListSchedule(seq)
only_sheep(prev, curr) = nparts(curr,:Wolf) == 0
overall = WhileSchedule(step, :main, only_sheep);


G, coords = initialize(2, .25, .25)
res = apply_schedule(step, G=G, verbose=false)
view_traj(res, Graph; positions=coords)