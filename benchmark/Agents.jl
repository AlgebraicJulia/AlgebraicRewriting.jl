# Benchmark AlgebraicRewriting against Agents.jl
using BenchmarkTools
const SUITE = BenchmarkGroup()

using AlgebraicRewriting

using Agents, Random, CairoMakie

# Sheep wolf model: Agents.jl
#############################

# Should be kept in sync with:
# https://juliadynamics.github.io/Agents.jl/stable/examples/predator_prey/

# Declare agents
#---------------

@agent Sheep GridAgent{2} begin
  energy::Float64
  reproduction_prob::Float64
  Δenergy::Float64
end

@agent Wolf GridAgent{2} begin
  energy::Float64
  reproduction_prob::Float64
  Δenergy::Float64
end

function initialize_model(; 
  n_sheep = 100, n_wolves = 50, dims = (20, 20), regrowth_time = 30, 
  Δenergy_sheep = 4, Δenergy_wolf = 20, sheep_reproduce = 0.04, 
  wolf_reproduce = 0.05, seed = 23182)

  rng = MersenneTwister(seed)
  space = GridSpace(dims, periodic = true)
  # Model properties contain the grass as two arrays: whether it is fully grown
  # and the time to regrow. Also have static parameter `regrowth_time`.
  # Notice how the properties are a `NamedTuple` to ensure type stability.
  properties = (
    fully_grown = falses(dims), countdown = zeros(Int, dims),
    regrowth_time = regrowth_time,
  )
  model = ABM(Union{Sheep, Wolf}, space;
    properties, rng, scheduler = Schedulers.randomly, warn = false
  )
  # Add agents
  for _ in 1:n_sheep
    energy = rand(model.rng, 1:(Δenergy_sheep*2)) - 1
    add_agent!(Sheep, model, energy, sheep_reproduce, Δenergy_sheep)
  end
  for _ in 1:n_wolves
    energy = rand(model.rng, 1:(Δenergy_wolf*2)) - 1
    add_agent!(Wolf, model, energy, wolf_reproduce, Δenergy_wolf)
  end
  # Add grass with random initial growth
  for p in positions(model)
    fully_grown = rand(model.rng, Bool)
    countdown = fully_grown ? regrowth_time : rand(model.rng, 1:regrowth_time) - 1
    model.countdown[p...] = countdown
    model.fully_grown[p...] = fully_grown
  end
  return model
end

# Stepping functions
#-------------------
function sheepwolf_step!(sheep::Sheep, model)
  randomwalk!(sheep, model)
  sheep.energy -= 1
  if sheep.energy < 0
    remove_agent!(sheep, model)
    return
  end
  eat!(sheep, model)
  if rand(model.rng) ≤ sheep.reproduction_prob
    reproduce!(sheep, model)
  end
end

function sheepwolf_step!(wolf::Wolf, model)
  randomwalk!(wolf, model; ifempty=false)
  wolf.energy -= 1
  if wolf.energy < 0
    remove_agent!(wolf, model)
    return
  end
  # If there is any sheep on this grid cell, it's dinner time!
  dinner = first_sheep_in_position(wolf.pos, model)
  !isnothing(dinner) && eat!(wolf, dinner, model)
  if rand(model.rng) ≤ wolf.reproduction_prob
    reproduce!(wolf, model)
  end
end

function first_sheep_in_position(pos, model)
  ids = ids_in_position(pos, model)
  j = findfirst(id -> model[id] isa Sheep, ids)
  isnothing(j) ? nothing : model[ids[j]]::Sheep
end

function eat!(sheep::Sheep, model)
  if model.fully_grown[sheep.pos...]
    sheep.energy += sheep.Δenergy
    model.fully_grown[sheep.pos...] = false
  end
  return
end

function eat!(wolf::Wolf, sheep::Sheep, model)
  remove_agent!(sheep, model)
  wolf.energy += wolf.Δenergy
  return
end

function reproduce!(agent::A, model) where {A}
  agent.energy /= 2
  id = nextid(model)
  offspring = A(id, agent.pos, agent.energy, agent.reproduction_prob, agent.Δenergy)
  add_agent_pos!(offspring, model)
  return
end

function grass_step!(model)
  @inbounds for p in positions(model) # we don't have to enable bound checking
    if !(model.fully_grown[p...])
      if model.countdown[p...] ≤ 0
        model.fully_grown[p...] = true
        model.countdown[p...] = model.regrowth_time
      else
        model.countdown[p...] -= 1
      end
    end
  end
end

# Running the model 
offset(a) = a isa Sheep ? (-0.1, -0.1*rand()) : (+0.1, +0.1*rand())
ashape(a) = a isa Sheep ? :circle : :utriangle
acolor(a) = a isa Sheep ? RGBAf(1.0, 1.0, 1.0, 0.8) : RGBAf(0.2, 0.2, 0.3, 0.8)
grasscolor(model) = model.countdown ./ model.regrowth_time
heatkwargs = (colormap = [:brown, :green], colorrange = (0, 1))

plotkwargs = (;
    ac = acolor, as = 25, am = ashape, offset, 
    scatterkwargs = (strokewidth = 1.0, strokecolor = :black), 
    heatarray = grasscolor, heatkwargs = heatkwargs,
)

fig, ax, abmobs = abmplot(initialize_model(); agent_step! = sheepwolf_step!, 
                          model_step! = grass_step!, plotkwargs...)

sheep(a) = a isa Sheep
wolf(a) = a isa Wolf
count_grass(model) = count(model.fully_grown)

steps = 1000
adata = [(sheep, count), (wolf, count)]
mdata = [count_grass]

function plot_population_timeseries(adf, mdf)
  figure = Figure(resolution = (600, 400))
  ax = figure[1, 1] = Axis(figure; xlabel = "Step", ylabel = "Population")
  sheepl = lines!(ax, adf.step, adf.count_sheep, color = :cornsilk4)
  wolfl = lines!(ax, adf.step, adf.count_wolf, color = RGBAf(0.2, 0.2, 0.3))
  grassl = lines!(ax, mdf.step, mdf.count_grass, color = :green)
  figure[1, 2] = Legend(figure, [sheepl, wolfl, grassl], ["Sheep", "Wolves", "Grass"])
  figure
end

stable_params = (;n_sheep = 140, n_wolves = 20, dims = (30, 30), Δenergy_sheep = 5,
  sheep_reproduce = 0.31, wolf_reproduce = 0.06, Δenergy_wolf = 30, seed = 71758)

SUITE["LotkaVolterra"]["Agents.jl2000"] = @benchmarkable begin
  sheepwolfgrass = initialize_model(;stable_params...)
  adf, mdf = run!(sheepwolfgrass, sheepwolf_step!, grass_step!, 2000; adata, mdata)
end
# plot_population_timeseries(adf, mdf)

# Make a video
abmvideo("sheepwolf.mp4", initialize_model(;stable_params...), sheepwolf_step!,
  grass_step!; frames = 100,framerate = 8,title = "Sheep Wolf Grass", plotkwargs...)

# Sheep wolf model: AlgebraicRewriting
######################################


using Catlab, DataMigrations, AlgebraicRewriting
const hom = homomorphism

@present TheoryWS <: SchGraph begin
  (Sheep, Wolf)::Ob
  sheep_loc::Hom(Sheep, V); wolf_loc::Hom(Wolf, V)
  Eng::AttrType
  countdown::Attr(V, Eng); 
  sheep_eng::Attr(Sheep, Eng); wolf_eng::Attr(Wolf, Eng)
end

@present TheoryWS′ <: TheoryWS begin
  Coord::AttrType
  coord::Attr(V, Coord)
end

@acset_type WS_Generic(TheoryWS, part_type=BitSetParts) <: HasGraph
const WS = WS_Generic{Int}

@acset_type WS′_Generic(TheoryWS′, part_type=BitSetParts) <: HasGraph
const WS′ = WS′_Generic{Int,Tuple{Int,Int}}

F = Migrate(
  Dict(:Sheep => :Wolf, :Wolf => :Sheep),
  Dict([:sheep_loc => :wolf_loc, :wolf_loc => :sheep_loc,
    :sheep_eng => :wolf_eng, :wolf_eng => :sheep_eng,
    :countdown => :countdown]), TheoryWS, WS)
F2 = Migrate(TheoryWS, WS, TheoryWS′, WS′; delta=false)

#=
Create an n × n grid with periodic boundary conditions. Edges in each cardinal
direction originate at every point

(i,j+1) -> (i+1,j+1) -> ...
  ↑          ↑
(i,j)   -> (i+1,j)   -> ...
=#

function create_grid(n::Int)
  lv = WS′()
  coords = Dict()
  for i in 0:n-1  # Initialize grass 50% green, 50% uniformly between 0-30
    for j in 0:n-1
      coords[i=>j] = add_part!(lv, :V; countdown=max(0, rand(-30:30)), coord=(i, j))
    end
  end
  for i in 0:n-1
    for j in 0:n-1
      add_part!(lv, :E; src=coords[i=>j], tgt=coords[mod(i + 1, n)=>j])
      add_part!(lv, :E; src=coords[i=>j], tgt=coords[mod(i - 1, n)=>j])
      add_part!(lv, :E; src=coords[i=>j], tgt=coords[i=>mod(j + 1, n)])
      add_part!(lv, :E; src=coords[i=>j], tgt=coords[i=>mod(j - 1, n)])
    end
  end
  lv
end

# # Rules

yWS = yoneda_cache(WS; clear=true);
yWS = yoneda_cache(WS; clear=false);

# Empty agent type
I = WS()
# Generic sheep agent
S = @acset_colim yWS begin s::Sheep end
# Generic wolf agent
W = F(S)
# Generic grass agent
G = @acset_colim yWS begin v::V end

N = Names(Dict("W" => W, "S" => S, "G" => G, "" => I));

# Moving forward

s_fwd_l = @acset_colim yWS begin e::E; s::Sheep; sheep_loc(s) == src(e) end
s_fwd_i = @acset_colim yWS begin e::E end
s_fwd_r = @acset_colim yWS begin e::E; s::Sheep; sheep_loc(s) == tgt(e) end

sheep_fwd_rule = Rule(
  hom.(Ref(s_fwd_i), [s_fwd_l, s_fwd_r]; monic=true)...,
  expr=(Eng=Dict(3 => vs -> vs[3] - 1),)
)

sheep_fwd = tryrule(RuleApp(:move_fwd, sheep_fwd_rule,
                            hom.(Ref(S), [s_fwd_l, s_fwd_r])...))


# Eat grass 

s_eat_pac = @acset_colim yWS begin s::Sheep; countdown(sheep_loc(s)) == 0 end

se_rule = Rule(S; expr=(Eng=[vs -> vs[1] + 4, vs -> 30],),
               ac=[PAC(hom(S, s_eat_pac))])
sheep_eat = tryrule(RuleApp(:Sheep_eat, se_rule, S))

# Eat sheep
w_eat_l = @acset_colim yWS begin s::Sheep; w::Wolf; sheep_loc(s) == wolf_loc(w) end
we_rule = Rule(hom(W, w_eat_l), id(W); expr=(Eng=[vs -> vs[3] + 20, vs -> vs[1]],))
wolf_eat = tryrule(RuleApp(:Wolf_eat, we_rule, W))


# Die if 0 eng
s_die_l = @acset_colim yWS begin s::Sheep; sheep_eng(s) == 0 end
sheep_die_rule = Rule(hom(G, s_die_l), id(G))
sheep_starve = RuleApp(:starve, sheep_die_rule, hom(S, s_die_l), create(G))

       
# Reproduction
s_reprod_r = @acset_colim yWS begin (x, y)::Sheep; sheep_loc(x) == sheep_loc(y) end

sheep_reprod_rule = Rule(
  hom(G, S), hom(G, s_reprod_r);
  expr=(Eng=[vs -> vs[2], fill(vs -> round(Int, vs[1] / 2, RoundUp), 2)...],)
)

sheep_reprod = RuleApp(:reproduce, sheep_reprod_rule,
  id(S), hom(S, s_reprod_r)) |> tryrule
  
# Grass increment

g_inc_n = deepcopy(G)
set_subpart!(g_inc_n, 1, :countdown, 0)
rem_part!(g_inc_n, :Eng, 1)

g_inc_rule = Rule(G; ac=[NAC(hom(G, g_inc_n))],
                  expr=(Eng=[vs -> only(vs) - 1],))
g_inc = RuleApp(:GrassIncrements, g_inc_rule, G) |> tryrule

# Scheduling Rules

general = mk_sched((;), (init=:S,), N, (
    maybe=const_cond([0.1, 0.9], S; name=:reprod),
    weak=Weaken(create(S)),
    fwd=sheep_fwd,
    repro=sheep_reprod,
    starve=sheep_starve),
  quote
    dead, alive = starve(init)
    moved = fwd(alive)
    out_repro, out_no_repro = maybe(moved)
    (dead, [repro(out_repro), out_no_repro])
  end)

sheep_ = mk_sched((;), (dead=Symbol(""), init=:S,), N, (
  weak=Weaken(create(S)), gen=general, eat=sheep_eat), quote
  [dead, weak(eat(init))]
end)

sheep_ =  general ⋅  (id([I]) ⊗ (sheep_eat ⋅ Weaken(create(S))) ⋅ merge_wires(I))
wolf_ = F(general) ⋅  (id([I]) ⊗ (wolf_eat ⋅ Weaken(create(W))) ⋅ merge_wires(I)) # once per wolf

# Do all sheep, then all wolves, then all daily operations
cycle = (agent(sheep_; n=:sheep, ret=I)
         ⋅
         agent(wolf_; n=:wolves, ret=I)
         ⋅
         agent(g_inc; n=:grass))

overall = while_schedule(cycle, curr -> nparts(curr, :Wolf) >= 0) |> F2  # wrap in a while loop

m = initialize_model(;stable_params...)

"""Convert an Agents.jl model state into an ACSet to compare apples to apples"""
function agents_to_algrw(m::StandardABM)::WS′
  (n, n′) = size(m.space.stored_ids)
  n == n′ || error("Must be a square grid")
  g = create_grid(n)
  for a in values(m.agents)
    A, E, P = a isa Sheep ? (:Sheep, :sheep_eng, :sheep_loc) : (:Wolf, :wolf_eng, :wolf_loc)
    add_part!(g, A; Dict(E => a.energy, P=>only(incident(g, a.pos .- 1, :coord)))...)
  end
  g
end

X = agents_to_algrw(initialize_model(;stable_params...))

SUITE["LotkaVolterra"]["AlgRW100"] = @benchmarkable begin
  res = interpret(overall, deepcopy(X); maxstep=100);
end
