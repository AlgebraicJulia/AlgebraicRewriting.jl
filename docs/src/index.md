# AlgebraicRewriting.jl

Here we walk through basic examples of double-pushout (DPO), single-pushout
(SPO), and sesqui-pushout (SqPO) rewriting. We also consider the rewriting of
graphs, Petri nets, and 2D semisimplicial sets (which are all instances of
rewriting in C-set categories) in addition to rewriting C-set slice categories
and structured cospans of C-sets. Future work will allow us to perform rewriting
of diagrams in C-set categories.

## Double pushout rewriting of graphs

This is the classic setting of graph transformation. Suppose we wish to rewrite
this graph:

```@example X
using Catlab, Catlab.Graphs, Catlab.Graphics, Catlab.CategoricalAlgebra

G = @acset Graph begin
    V=3; E=3;
    src=[1,2,2];
    tgt=[2,3,3]
end
to_graphviz(G; node_labels=true) # hide
```

Our rewrite rule will look for parallel arrows

```@example X
L = @acset Graph begin V=2; E=2; src=1; tgt=2 end # matched pattern
to_graphviz(L; node_labels=true) # hide
```

Then remove one of the edges (by defining the *non-deleted* subpart of the
pattern as the following graph)

```@example X
I = @acset Graph begin V=2; E=1; src=1; tgt=2 end # interface: non-deleted subset of L
to_graphviz(I; node_labels=true) # hide
```

And lastly replacing the pattern with one that collapses the two matched
vertices to form a loop.

```@example X
R = @acset Graph begin V=1; E=1; src=1; tgt=1 end # Replacement pattern
to_graphviz(R; node_labels=true) # hide
```

We assemble this information into a rewrite rule by forming a span `L ↩ I → R`
```@example X
using AlgebraicRewriting
using AlgebraicRewriting: rewrite
const hom = homomorphism
rule = Rule(hom(I,L), hom(I,R))
H = rewrite(rule, G)
to_graphviz(H; node_labels=true) # hide
```

Something to note here is that the result is only defined up to isomorphism,
e.g. the vertex which corresponded to vertex #1 in the original graph may not
be #1 in the result.

As the example `mesh.jl`, shows, we are not limited to rewriting
(directed multi-) graphs - we can rewrite triangle meshes with the same
methodology: we provide an instance of the datatype to serve as our pattern
for replacement (such as the quadrangle above) and then need an instance to
serve as our non-deleted subset of that pattern.

![Alt Text](assets/meshres.png)


## Applied example: Lotka-Volterra agent-based model

### Overview
The aim to recapture the dynamics of NetLogo's
[Wolf Sheep predation](https://ccl.northwestern.edu/netlogo/models/WolfSheepPredation)
model in terms of declarative rewrite rules, rather than standard code-based
interface. This models wolves in sheeps living in a periodic 2-D space, which is
also covered by grass. Wolves eat sheep to gain energy, sheep eat grass to gain
energy, and grass takes time to grow back after it has been eaten. Each
wolf/sheep has a direction and is moving in that direction (veering left or
right randomly with some probability). At some rate, wolves/sheep undergo
mitosis and their energy is split in half. As the wolves/sheep move, they lose
energy, and they die if they are eaten or run out of energy. The simulation
could go on indefinitely, or it could be ended when one of the two species
completely dies out.

The main difference with our reconstruction of the NetLogo model is that we
model the 2D space as a discrete grid. This is more amenable to the style of
pattern matching characteristic of AlgebraicRewriting, in contrast to floating
point coordinates and collision checking to see when two entities occupy the
same space.

The following code snippets come from [this file](https://github.com/AlgebraicJulia/AlgebraicRewriting.jl/blob/main/docs/src/lotka_volterra.jl).

### Defining the datatype we are rewriting

```julia
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
```

- `grassval == 0` means alive grass; `grassval > 0` represents the time 
  until the grass is alive.
- Sheeps and wolves have position and direction.

There is a certain symmetry between wolves and sheep in the schema, which we can
make explicit with the following endofunctor:

```julia
F = FinFunctor(
  Dict([:Sheep => :Wolf, :Wolf => :Sheep, :V=>:V, :E=>:E,:Dir=>:Dir, :Eng=>:Eng]),
  Dict([:sheep_loc=>:wolf_loc, :wolf_loc=>:sheep_loc,
        :sheep_eng=>:wolf_eng, :wolf_eng=>:sheep_eng,:grass_eng =>:grass_eng,
        :sheep_dir=>:wolf_dir, :wolf_dir=>:sheep_dir,
        :src=>:src,:tgt=>:tgt,:dir=>:dir]),
  TheoryLV, TheoryLV
)
```

We can apply `F` to a rewrite rule defined for sheep (e.g. that one dies when it
has zero energy) and obtain the analogous rule for wolves without any effort.

### Rules and Schedules

We can declare a `Rule` and how we wish to schedule that rule.
The 'outer loop' is a `while_schedule` that executes all the rules in some order
(i.e. a `LinearSchedule` wrapped around a list called `seq` made up of
individual `RuleSchedule`s).

```julia
extinct(prev, curr) = nparts(curr, :Wolf) == 0 || nparts(curr, :Sheep) == 0
overall = while_schedule(ListSchedule(seq), :main, extinct, 10);
```

Let's show some of the things that went into `seq`. Below we define sheep
reproduction to occur with probability 0.04 and wolf reproduction to occur with
probability 0.05.

```julia
s_reprod_l =  @acset LV begin
  Sheep=1; V=1; sheep_loc=1; grass_eng=[Var(:_1)]
  sheep_dir=[Var(:_2)]; sheep_eng=[Var(:a)]; 
end
```

This defines a *pattern* which we wish to match. The suffix `_l` indicates that
this is the `L` of a rewrite rule, which is a partial map `L → R`, i.e.
`L ↩ I → R`.

We need to define the interface `I`, which contains the subobject of `L` which
is *not deleted*.

```julia
s_reprod_i = @acset LV begin V=1; grass_eng=[Var(:_1)] end
```

and the right object, `R`, includes things that are added. We're removing a
sheep with energy `a` at a certain position and replace it with two sheep with
`a/2` energy.

```julia
s_reprod_r =  @acset LV begin
  Sheep=2; V=1; sheep_loc=1; grass_eng=[Var(:_1)]
  sheep_dir=[Var(:_2),Var(:_2)]; 
  sheep_eng=fill(:(round(Int, a/2, RoundUp)), 2); 
end
```

We assemble this data into a rewrite rule.

```julia
sheep_reprod = Rule(hom(s_reprod_i,s_reprod_l),
                    hom(s_reprod_i,s_reprod_r));
```

As mentioned before, we can turn this into a wolf reproduction rule by applying
our functor. Then we add the two rules along with their probabilities. The
`false` here refers to whether or not we apply the rule only once or whether we
apply it for every match we find (which is what we want to do, to give *each*
sheep a 4% chance of reproducing).

```julia
wolf_reprod = F(sheep_reprod)
```


```julia
append!(seq, [RuleSchedule(sheep_reprod,:sheep_reprod, false,0.04),
              RuleSchedule(wolf_reprod, :wolf_reprod, false,0.05)]);
```

Note that our pattern `L` can have `Var` variables, and our right hand side `R`
can have Julia expressions involving those variables.

Another illustrative example is the 'move forward' rule. We simultaneously
advance the sheep forward one space and decrement its energy by 1.

```julia
s_move_forward_l = @acset LV begin
  Sheep=1; V=2; E=1; sheep_loc=1;
  src=1; tgt=2; dir=[Var(:z)]; 
  grass_eng=Var.([:_1,:_2])
  sheep_dir=[Var(:z)]; sheep_eng=[Var(:x)]
end
```

This pattern has two contiguous edges that are in the same direction (implicitly
constrained by using `Var(:a)` twice) and the sheep in the first position.

```julia
s_move_forward_i = deepcopy(s_move_forward_l)
rem_part!(s_move_forward_i, :Sheep, 1)

s_move_forward_r = deepcopy(s_move_forward_i)
add_part!(s_move_forward_r, :Sheep; sheep_loc=2, sheep_eng=:(x-1), sheep_dir=Var(:z))
```

We delete the sheep and recreate one in position #2, with one fewer energy unit.
However, this is only valid if the sheep has any energy. To prevent this rule
from firing, we need a *negative application condition*. This embeds the
pattern `L` in a larger context `N` that has the semantics of: if `L` *and* `N`
are matched, then, actually, don't fire the rule. The pattern we want to avoid
is one where the sheep has zero energy.

```julia
s_move_n = deepcopy(s_move_forward_l)
set_subpart!(s_move_n, 1, :sheep_eng, 0)

sheep_move_forward = Rule(
  hom(s_move_forward_i, s_move_forward_l; monic=true),
  hom(s_move_forward_i, s_move_forward_r; monic=true),
  [NAC(hom(s_move_forward_l, s_move_n; monic=true))]
)

wolf_move_forward = F(sheep_move_forward)
```

In all these cases, automatic homomorphism finding is sufficient for obtaining
the morphism data of `L ↩ I → R`.

### Other functions
Functions to initialize and visualize the world-states are defined in the file
[lotka_volterra.jl](https://github.com/AlgebraicJulia/AlgebraicRewriting.jl/blob/main/docs/src/lotka_volterra.jl). 
Important functionality only possible in the notebook is the
ability to move a slider and view the progression of a simulation.

![Alt Text](assets/slider2.gif)

## Alternative rewriting semantics
A nice property of DPO is that you can analyze the relationship between `I` and
`L` to see exactly what will be deleted (likewise for `I` and `R` to see what
will be added). However, this is sometimes not what we want: we wish to delete
*outside the context* `L`, or to implicitly create things. The former is
possible in single pushout rewriting, and both are possible in sesqui pushout
rewriting.

### Single pushout rewriting
Implicit deletion works like a cascading delete: if you delete a vertex
(for example), then you implicitly delete an edge which refers to that vertex.

```@example X
L = ACSetTransformation(Graph(), Graph(1)) # a vertex is deleted
R = id(Graph()) # nothing is added
r = Rule{:SPO}(L,R)
m = hom(Graph(1), path_graph(Graph, 3)) # rewriting • → • → •
res = rewrite_match(r,m)
to_graphviz(res; node_labels=true) # hide
```

### Sesqui pushout rewriting

Here our rewrite rule takes a vertex and duplicates it. Sesqui pushout rewriting
allows "implicit copying", so copying a vertex that is connected to another via
an edge will create a new connected vertex, rather than an isolated vertex.

```@example X
L = hom(Graph(2), Graph(1))
R = id(Graph(2))
r = Rule{:SqPO}(L,R)
m = hom(Graph(1), path_graph(Graph, 2)) # rewriting • → •
res = rewrite_match(r,m)
to_graphviz(res; node_labels=true) # hide
```

## Rewriting things that aren't C-Sets

Anything that implements some basic features (e.g. `pushout`,
`pushout_complement`) can be used with this rewriting infrastructure. Generally,
these are constructions that are built on top of C-Sets.

### Slices

The category-theoretic notion of a *slice* allows us to consider a mapping
between objects as an object itself. AlgebraicRewriting then allows us to
implement rewriting these slice objects.

In general it is difficult to visualize examples of slice rewriting .
Luckily, it turns out *Petri nets* (which are visualized in
[AlgebraicPetri](https://github.com/AlgebraicJulia/AlgebraicPetri.jl),
where they are used to model
chemical reaction networks) are equivalent to a certain kind of slice in graph.
Therefore we will use AlgebraicPetri's visualization code to represent graph
homomorphisms into this following graph:

```@example X
two = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,1] end
to_graphviz(two; node_labels=true) # hide
```

Vertices that are sent to vertex #1 will be thought of as "species", whereas
vertices that are sent to vertex #2 will be thought of as "transitions". Whether
or not the edge is from a transition or to a transition determines whether it
will correspond to an "input" or an "output", and the fact there exists a
homomorphism into `two` at all guarantees there are no species-species or
transition-transition edges.

To rewrite a slice, we first need a pattern slice. We start with the graph
that will be made into a slice by giving a homomorphism into `two`:
```@example X
L_ = path_graph(Graph, 2)
to_graphviz(L_; node_labels=true) # hide
```
Then we turn this into a slice

```@example X
using AlgebraicPetri
function graph_slice(s::Slice)  # hide
    h = s.slice  # hide
    V, E = collect.([h[:V], h[:E]])  # hide
    g = dom(h)  # hide
    (S,T), (I,O) = [[findall(==(i),X) for i in 1:2] for X in [V,E]]  # hide
    nS,nT,nI,nO = length.([S,T,I,O])  # hide
    findS, findT = [x->findfirst(==(x), X) for X in [S,T]]  # hide
    AlgebraicPetri.Graph(@acset AlgebraicPetri.PetriNet begin  # hide
        S=nS; T=nT; I=nI; O=nO  # hide
        is=findS.(g[I,:src]); it=findT.(g[I, :tgt])  # hide
        ot=findT.(g[O,:src]); os=findS.(g[O, :tgt]) end)  # hide
end; # hide

L = Slice(ACSetTransformation(L_, two, V=[2,1], E=[2]))
graph_slice(L) # hide
```

```@example X
I = Slice(ACSetTransformation(Graph(1), two, V=[2]))

R = Slice(ACSetTransformation(Graph(2), two, V=[2, 1]))
graph_slice(R) # hide
```
Thus our rewrite rule will delete an *output* edge.

```@example X
rule = Rule(hom(I, L), hom(I, R));
```

The instance of a slice we are rewriting:
```@example X
G_ = path_graph(Graph, 3)
G = Slice(ACSetTransformation(G_, two, V=[1,2,1], E=[1,2]))
graph_slice(G) # hide
```

```@example X
using AlgebraicRewriting: rewrite # hide
H = rewrite(rule, G)
graph_slice(H) # hide
```

### Coming: Structured cospans and Diagrams