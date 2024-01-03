```@meta
EditURL = "../../literate/lotka_volterra.jl"
```

````@example lotka_volterra
using Catlab, Catlab.Theories, Catlab.CategoricalAlgebra, Catlab.Graphs,
  Catlab.Graphics, Catlab.WiringDiagrams, Catlab.Programs
using AlgebraicRewriting
using Random, Test, StructEquality
using Luxor

Random.seed!(123);

using Catlab.Graphics.Graphviz: Attributes, Statement, Node
using Catlab.Graphics.Graphviz

import Catlab.CategoricalAlgebra: left, right

function right(s::Symbol)
  if s == :N
    return :E
  elseif s == :S
    return :W
  elseif s == :E
    return :S
  elseif s == :W
    return :N
  end
end
function left(s::Symbol)
  if s == :N
    return :W
  elseif s == :S
    return :E
  elseif s == :E
    return :N
  elseif s == :W
    return :S
  end
end

"""
Grass = 0 means alive grass, whereas grass > 0 represent a counter of time until
the grass is alive.

Sheeps and wolves have position and direction, so we assign each an *edge*. We
assume a convention where the location of the something is the edge SOURCE.

Dir is an attribute which can take values :N, :E, :W, and :S.
"""
@present TheoryLV <: SchGraph begin
  (Sheep, Wolf)::Ob
  sheep_loc::Hom(Sheep, V)
  wolf_loc::Hom(Wolf, V)

  (Dir, Eng)::AttrType
  grass_eng::Attr(V, Eng)
  sheep_eng::Attr(Sheep, Eng)
  wolf_eng::Attr(Wolf, Eng)
  sheep_dir::Attr(Sheep, Dir)
  wolf_dir::Attr(Wolf, Dir)
  dir::Attr(E, Dir)
end

@present TheoryLV′ <: TheoryLV begin
  Coord::AttrType
  coord::Attr(V, Coord)
end

to_graphviz(TheoryLV; prog="dot")

@acset_type LV_Generic(TheoryLV) <: HasGraph
const LV = LV_Generic{Symbol,Int}

@acset_type LV′_Generic(TheoryLV′) <: HasGraph
const LV′ = LV′_Generic{Symbol,Int,Tuple{Int,Int}}

F = Migrate(
  Dict(:Sheep => :Wolf, :Wolf => :Sheep),
  Dict([:sheep_loc => :wolf_loc, :wolf_loc => :sheep_loc,
    :sheep_eng => :wolf_eng, :wolf_eng => :sheep_eng, :grass_eng => :grass_eng,
    :sheep_dir => :wolf_dir, :wolf_dir => :sheep_dir,]), LV)
F2 = Migrate(
  Dict(x => x for x in Symbol.(TheoryLV.generators[:Ob])),
  Dict(x => x for x in Symbol.(TheoryLV.generators[:Hom])), LV′; delta=false)

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
  for i in 0:n-1
    for j in 0:n-1
      coords[i=>j] = add_part!(lv, :V; grass_eng=max(0, rand(-30:30)), coord=(i, j))
    end
  end
  for i in 0:n-1
    for j in 0:n-1
      add_part!(lv, :E; src=coords[i=>j], tgt=coords[mod(i + 1, n)=>j], dir=:E)
      add_part!(lv, :E; src=coords[i=>j], tgt=coords[mod(i - 1, n)=>j], dir=:W)
      add_part!(lv, :E; src=coords[i=>j], tgt=coords[i=>mod(j + 1, n)], dir=:N)
      add_part!(lv, :E; src=coords[i=>j], tgt=coords[i=>mod(j - 1, n)], dir=:S)
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
    for _ in 1:round(Int, n_ * n^2)
      dic = Dict([eng => 5, loc => rand(vertices(grid)),
        d => rand([:N, :E, :S, :W])])
      add_part!(grid, name; dic...)
    end
  end
  return grid
end


supscript_d = Dict([
  '1' => '¹', '2' => '²', '3' => '³', '4' => '⁴', '5' => '⁵', '6' => '⁶', '7' => '⁷', '8' => '⁸',
  '9' => '⁹', '0' => '⁰', 'x' => 'ˣ', 'y' => 'ʸ', 'z' => 'ᶻ', 'a' => 'ᵃ', 'b' => 'ᵇ', 'c' => 'ᶜ',
  'd' => 'ᵈ'])
supscript(x::String) = join([get(supscript_d, c, c) for c in x])

"""Visualize a LV"""
function view_LV(p::ACSetTransformation, pth=tempname(); name="G", title="")
  if nparts(dom(p), :Wolf) == 1
    star = :Wolf => p[:Wolf](1)
  elseif nparts(dom(p), :Sheep) == 1
    star = :Sheep => p[:Sheep](1)
  elseif nparts(dom(p), :V) == 1
    star = :V => p[:V](1)
  else
    star = nothing
  end
  view_LV(codom(p), pth; name=name, title=title, star=star)
end
function view_LV(p::LV′, pth=tempname(); name="G", title="", star=nothing)
  pstr = ["$(i),$(j)!" for (i, j) in p[:coord]]
  stmts = Statement[]
  for s in 1:nv(p)
    st = (star == (:V => s)) ? "*" : ""
    gv = p[s, :grass_eng]
    col = gv == 0 ? "lightgreen" : "tan"
    push!(stmts, Node("v$s", Attributes(
      :label => gv == 0 ? "" : string(gv) * st,
      :shape => "circle",
      :color => col, :pos => pstr[s])))
  end
  d = Dict([:E => (1, 0), :N => (0, 1), :S => (0, -1), :W => (-1, 0),])

  args = [(:true, :Wolf, :wolf_loc, :wolf_eng, :wolf_dir),
    (false, :Sheep, :sheep_loc, :sheep_eng, :sheep_dir)]

  for (is_wolf, prt, loc, eng, dr) in args
    for w in parts(p, prt)
      st = (star == ((is_wolf ? :Wolf : :Sheep) => w)) ? "*" : ""
      e = only(incident(p, p[w, loc], :src) ∩ incident(p, p[w, dr], :dir))
      s = src(p, e)
      dx, dy = d[p[e, :dir]]
      (sx, sy) = p[s, :coord]

      L, R = 0.25, 0.1
      wx = sx + L * dx + R * rand()
      wy = sy + L * dy + R * rand()
      ID = "$(is_wolf ? :w : :s)$w"
      append!(stmts, [Node(ID, Attributes(
        :label => "$w" * supscript("$(p[w,eng])") * st,
        :shape => "square", :width => "0.3px", :height => "0.3px", :fixedsize => "true",
        :pos => "$(wx),$(wy)!", :color => is_wolf ? "red" : "lightblue"))])
    end
  end

  g = Graphviz.Digraph(name, Statement[stmts...]; prog="neato",
    graph_attrs=Attributes(:label => title, :labelloc => "t"),
    node_attrs=Attributes(:shape => "plain", :style => "filled"))
  open(pth, "w") do io
    show(io, "image/svg+xml", g)
  end
end

i1 = initialize(2, 0.5, 0.5)
````

view_LV(i1)

RULES

````@example lotka_volterra
#######
yLV = yoneda_cache(LV; clear=true);
yLV = yoneda_cache(LV; clear=false);
nothing #hide
````

Empty agent type

````@example lotka_volterra
I = LV()
````

Generic sheep agent

````@example lotka_volterra
S = @acset_colim yLV begin
  s::Sheep
end
````

Generic wolf agent

````@example lotka_volterra
W = F(S)
````

Generic grass agent

````@example lotka_volterra
G = @acset_colim yLV begin
  v::V
end

N = Names(Dict("W" => W, "S" => S, "G" => G, "" => I))
````

Rotating

````@example lotka_volterra
rl = Rule(id(S), id(S); expr=(Dir=[xs -> left(only(xs))],))
rr = Rule(id(S), id(S); expr=(Dir=[xs -> right(only(xs))],))

sheep_rotate_l = tryrule(RuleApp(:turn_left, rl, S))
sheep_rotate_r = tryrule(RuleApp(:turn_right, rr, S))
````

we can imagine executing these rules in sequence or in parallel

````@example lotka_volterra
seq_sched = (sheep_rotate_l ⋅ sheep_rotate_r)
````

view_sched(seq_sched; names=N)

````@example lotka_volterra
par_sched = (sheep_rotate_l ⊗ sheep_rotate_r)
````

view_sched(par_sched; names=N)

````@example lotka_volterra
begin
  ex = @acset_colim yLV begin
    e::E
    s::Sheep
    sheep_loc(s) == src(e)
    sheep_dir(s) == :N
  end
  expected = copy(ex)
  expected[:sheep_dir] = :W
  @test is_isomorphic(rewrite(rl, ex), expected)
end
````

Moving forward

````@example lotka_volterra
s_fwd_l = @acset_colim yLV begin
  e::E
  s::Sheep
  sheep_loc(s) == src(e)
end
s_fwd_i = @acset_colim yLV begin
  e::E
end
s_fwd_r = @acset_colim yLV begin
  e::E
  s::Sheep
  sheep_loc(s) == tgt(e)
end
s_n = @acset_colim yLV begin
  e::E
  s::Sheep
  sheep_loc(s) == src(e)
  sheep_eng(s) == 0
end

sheep_fwd_rule = Rule(
  homomorphism(s_fwd_i, s_fwd_l; monic=true),
  homomorphism(s_fwd_i, s_fwd_r; monic=true),
  ac=[AppCond(homomorphism(s_fwd_l, s_n), false)],
  expr=(Eng=Dict(3 => vs -> vs[3] - 1), Dir=Dict(2 => vs -> vs[2]))
)

sheep_fwd = tryrule(RuleApp(:move_fwd, sheep_fwd_rule,
  homomorphism(S, s_fwd_l), homomorphism(S, s_fwd_r)))


sheep_fwd_rule.L |> codom

begin # test
  ex = @acset_colim yLV begin
    (e1, e2)::E
    s::Sheep
    sheep_loc(s) == tgt(e1)
    tgt(e1) == src(e2)
    sheep_dir(s) == :N
    sheep_eng(s) == 10
  end
  expected = @acset_colim yLV begin
    (e1, e2)::E
    s::Sheep
    sheep_loc(s) == tgt(e2)
    tgt(e1) == src(e2)
    sheep_dir(s) == :N
    sheep_eng(s) == 9
  end
  @test is_isomorphic(expected, rewrite(sheep_fwd_rule, ex))
end
````

Eat grass + 4eng

Grass is at 0 - meaning it's ready to be eaten

````@example lotka_volterra
s_eat_pac = @acset_colim yLV begin
  s::Sheep
  grass_eng(sheep_loc(s)) == 0
end

se_rule = Rule(id(S), id(S); expr=(Eng=[vs -> vs[1] + 4, vs -> 30],),
  ac=[AppCond(homomorphism(S, s_eat_pac))])
sheep_eat = tryrule(RuleApp(:Sheep_eat, se_rule, S))

begin # test
  ex = @acset_colim yLV begin
    s::Sheep
    e::E
    sheep_loc(s) == tgt(e)
    sheep_eng(s) == 3
    grass_eng(tgt(e)) == 0
    grass_eng(src(e)) == 10
  end
  expected = @acset_colim yLV begin
    s::Sheep
    e::E
    sheep_loc(s) == tgt(e)
    sheep_eng(s) == 7
    grass_eng(tgt(e)) == 30
    grass_eng(src(e)) == 10
  end

  @test is_isomorphic(expected, rewrite(se_rule, ex))
end
````

Eat sheep + 20 eng

````@example lotka_volterra
w_eat_l = @acset_colim yLV begin
  s::Sheep
  w::Wolf
  sheep_loc(s) == wolf_loc(w)
end

we_rule = Rule(homomorphism(W, w_eat_l), id(W); expr=(Eng=[vs -> vs[3] + 20, vs -> vs[1]],))
wolf_eat = tryrule(RuleApp(:Wolf_eat, we_rule, W))

begin # test
  ex = @acset LV begin
    Sheep = 1
    Wolf = 1
    V = 3
    E = 2
    src = [1, 2]
    tgt = [2, 3]
    sheep_loc = 2
    sheep_eng = [3]
    grass_eng = [9, 10, 11]
    dir = fill(:N, 2)
    sheep_dir = [:N]
    wolf_loc = [2]
    wolf_eng = [16]
    wolf_dir = [:S]
  end
  expected = @acset LV begin
    Wolf = 1
    V = 3
    E = 2
    src = [1, 2]
    tgt = [2, 3]
    grass_eng = [9, 10, 11]
    dir = fill(:N, 2)
    sheep_dir = [:N]
    wolf_loc = [2]
    wolf_eng = [36]
    wolf_dir = [:S]
  end
  @test is_isomorphic(rewrite(we_rule, ex), expected)
end
````

Die if 0 eng

````@example lotka_volterra
s_die_l = @acset_colim yLV begin
  s::Sheep
  sheep_eng(s) == 0
end

sheep_die_rule = Rule(homomorphism(G, s_die_l), id(G))
sheep_starve = (RuleApp(:starve, sheep_die_rule,
  homomorphism(S, s_die_l), create(G))
                ⋅
                (id([I]) ⊗ Weaken(create(S))) ⋅ merge_wires(I))

begin # test
  ex = s_die_l ⊕ W
  expected = G ⊕ W
  @test is_isomorphic(rewrite(sheep_die_rule, ex), expected)
end
````

reproduction

````@example lotka_volterra
s_reprod_r = @acset_colim yLV begin
  (x, y)::Sheep
  sheep_loc(x) == sheep_loc(y)
end

sheep_reprod_rule = Rule(
  homomorphism(G, S),
  homomorphism(G, s_reprod_r);
  expr=(Dir=[vs -> vs[1], vs -> vs[1]], Eng=[vs -> vs[2],
    fill(vs -> round(Int, vs[1] / 2, RoundUp), 2)...],)
)

sheep_reprod = RuleApp(:reproduce, sheep_reprod_rule,
  id(S), homomorphism(S, s_reprod_r)) |> tryrule

begin # test
  ex = @acset_colim yLV begin
    s::Sheep
    w::Wolf
    sheep_eng(s) == 10
  end
  expected = @acset_colim yLV begin
    (s1, s2)::Sheep
    w::Wolf
    sheep_loc(s1) == sheep_loc(s2)
    sheep_eng(s1) == 5
    sheep_eng(s2) == 5
  end
  @test is_isomorphic(rewrite(sheep_reprod_rule, ex), expected)
end
````

Grass increment

````@example lotka_volterra
g_inc_n = deepcopy(G)
set_subpart!(g_inc_n, 1, :grass_eng, 0);
rem_part!(g_inc_n, :Eng, 1)

g_inc_rule = Rule(id(G), id(G);
  ac=[AppCond(homomorphism(G, g_inc_n), false)],
  expr=(Eng=[vs -> only(vs) - 1],))
g_inc = RuleApp(:GrassIncrements, g_inc_rule, G) |> tryrule


begin # test
  ex = @acset LV begin
    Sheep = 1
    V = 3
    E = 2
    src = [1, 2]
    tgt = [2, 3]
    sheep_loc = 2
    sheep_eng = [3]
    grass_eng = [1, 10, 2]
    dir = fill(:N, 2)
    sheep_dir = [:N]
  end
  expected = @acset LV begin
    Sheep = 1
    V = 3
    E = 2
    src = [1, 2]
    tgt = [2, 3]
    sheep_loc = 2
    sheep_eng = [3]
    grass_eng = [0, 10, 2]
    dir = fill(:N, 2)
    sheep_dir = [:N]
  end
  @test is_isomorphic(rewrite(g_inc_rule, ex), expected)
end
````

Scheduling Rules

````@example lotka_volterra
##################
````

Stuff that happens once per sheep

25% chance of left turn, 25% chance of right turn, 50% stay in same direction

````@example lotka_volterra
general = mk_sched((;), (init=:S,), N, (
    turn=const_cond([1.0, 2.0, 1.0], S; name=:turn),
    maybe=const_cond([0.1, 0.9], S; name=:reprod),
    lft=sheep_rotate_l,
    rght=sheep_rotate_r,
    fwd=sheep_fwd,
    repro=sheep_reprod,
    starve=sheep_starve),
  quote
    out_l, out_str, out_r = turn(init)
    moved = fwd([lft(out_l), out_str, rght(out_r)])
    out_repro, out_no_repro = maybe(moved)
    return starve([repro(out_repro), out_no_repro])
  end)

sheep = sheep_eat ⋅ general   # once per sheep
wolf = wolf_eat ⋅ F(general)  # once per wolf
````

Do all sheep, then all wolves, then all daily operations

````@example lotka_volterra
cycle = (agent(sheep; n=:sheep, ret=I)
         ⋅
         agent(wolf; n=:wolves, ret=I)
         ⋅
         agent(g_inc; n=:grass))
````

wrap in a while loop

````@example lotka_volterra
overall = while_schedule(cycle, curr -> nparts(curr, :Wolf) >= 0) |> F2
````

view_sched(overall; names=F2(N))

````@example lotka_volterra
X = initialize(3, 0.25, 0.25)
res, = apply_schedule(overall, X; steps=50);
nothing #hide
````

Run this lines to view the trajectory
view_traj(overall, res, view_LV; agent=true, names=F2(N))

