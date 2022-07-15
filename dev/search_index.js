var documenterSearchIndex = {"docs":
[{"location":"#AlgebraicRewriting.jl","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"","category":"section"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"Here we walk through basic examples of double-pushout (DPO), single-pushout (SPO), and sesqui-pushout (SqPO) rewriting. We also consider the rewriting of graphs, Petri nets, and 2D semisimplicial sets (which are all instances of rewriting in C-set categories) in addition to rewriting C-set slice categories and structured cospans of C-sets. Future work will allow us to perform rewriting of diagrams in C-set categories.","category":"page"},{"location":"#Double-pushout-rewriting-of-graphs","page":"AlgebraicRewriting.jl","title":"Double pushout rewriting of graphs","text":"","category":"section"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"This is the classic setting of graph transformation. Suppose we wish to rewrite this graph:","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"using Catlab, Catlab.Graphs, Catlab.Graphics, Catlab.CategoricalAlgebra\n\nG = @acset Graph begin\n    V=3; E=3;\n    src=[1,2,2];\n    tgt=[2,3,3]\nend\nto_graphviz(G; node_labels=true) # hide","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"Our rewrite rule will look for parallel arrows","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"L = @acset Graph begin V=2; E=2; src=1; tgt=2 end # matched pattern\nto_graphviz(L; node_labels=true) # hide","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"Then remove one of the edges (by defining the non-deleted subpart of the pattern as the following graph)","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"I = @acset Graph begin V=2; E=1; src=1; tgt=2 end # interface: non-deleted subset of L\nto_graphviz(I; node_labels=true) # hide","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"And lastly replacing the pattern with one that collapses the two matched vertices to form a loop.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"R = @acset Graph begin V=1; E=1; src=1; tgt=1 end # Replacement pattern\nto_graphviz(R; node_labels=true) # hide","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"We assemble this information into a rewrite rule by forming a span L ↩ I → R","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"using AlgebraicRewriting\nusing AlgebraicRewriting: rewrite\nconst hom = AlgebraicRewriting.homomorphism\nrule = Rule(hom(I,L), hom(I,R))\nH = rewrite(rule, G)\nto_graphviz(H; node_labels=true) # hide","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"Something to note here is that the result is only defined up to isomorphism, e.g. the vertex which corresponded to vertex #1 in the original graph may not be #1 in the result.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"As the following example shows, we are not limited to rewriting (directed multi-) graphs.","category":"page"},{"location":"#Double-pushout-rewriting-of-triangle-mesh","page":"AlgebraicRewriting.jl","title":"Double pushout rewriting of triangle mesh","text":"","category":"section"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"Suppose we want to perform rewriting on a mesh with triangles defined over certain triples of edges.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"using Catlab.Graphs.BasicGraphs: TheoryGraph\nusing CairoMakie, GeometryBasics # hide\nusing Base.Iterators # hide\nusing CombinatorialSpaces # hide\nimport AlgebraicPetri # hide\nusing CombinatorialSpaces.SimplicialSets: get_edge! # hide\n\n@present ThSemisimplicialSet  <: TheoryGraph begin\n  T :: Ob\n  (d1,d2,d3)::Hom(T,E)\n  compose(d1, src) == compose(d2, src)\n  compose(d1, tgt) == compose(d3, tgt)\n  compose(d2, tgt) == compose(d3, src)\nend\n@acset_type SSet(ThSemisimplicialSet)\n\nquadrangle = @acset SSet begin\n    T=2; E=5; V=4\n    d1=[1,1]; d2=[2,3]; d3=[4,5]\n    src=[1,1,1,2,3]\n    tgt=[4,2,3,4,4]\nend\n\nfunction plot_sset(ss::SSet, points::Vector, # hide\n                   tri_colors::Union{Nothing,Vector}=nothing) # hide\n    dflt = collect(take(cycle([:blue,:red,:green, :purple, :pink, :yellow, :grey, :orange, :brown, :cyan]), nparts(ss, :T))) # hide\n    tri_colors = isnothing(tri_colors) ? dflt : tri_colors # hide\n    # Validate inputs # hide\n    lengthscale=0.8 # hide\n    dim = length(points[1]) # hide\n    length(points) == nparts(ss,:V) || error(\"# of points\") # hide\n    if dim == 2 # hide\n        points = [(p1,p2,0.) for (p1,p2) in points] # hide\n    elseif dim != 3 # hide\n        error(\"dim $dim\") # hide\n    end # hide\n    tri_colors = tri_colors[1:nparts(ss, :T)] # hide\n\n    # Convert SSet to EmbeddedDeltaSet2D # hide\n    s = EmbeddedDeltaSet2D{Bool, Point{3, Float64}}() # hide\n\n    edge_colors = [:black for _ in nparts(ss, :E)] # hide\n    add_vertices!(s, length(points), point=points) # hide\n    for (src, tgt) in zip(ss[:src], ss[:tgt]) # hide\n        get_edge!(s, src, tgt) # hide\n    end # hide\n\n    for t in parts(ss,:T) # hide\n    glue_sorted_triangle!(s, ss[t,[:d1,:src]], # hide\n                             ss[t,[:d3,:src]], # hide\n                             ss[t, [:d1,:tgt]]) # hide\n    end # hide\n\n    # Split mesh into component triangles # hide\n  m = GeometryBasics.Mesh(s) # hide\n  x = faces(m) # hide\n  m_points = m.position[vcat([[t[1],t[2],t[3]] for t in x]...)] # hide\n  m_faces = TriangleFace{Int}[[((t-1) * 3) .+ (1,2,3) for t in  1:length(x)]...]  # hide\n  new_m = GeometryBasics.Mesh(Point{3, Float64}[m_points...], m_faces) # hide\n  if ntriangles(s) == 0  # hide\n     fig, ax, ob = arrows((s[s[:∂v0], :point] * (0.5 + lengthscale / 2)  # hide\n                            .+ s[s[:∂v1], :point] * (0.5 - lengthscale / 2)) ,  # hide\n                          (s[s[:∂v1], :point] .- s[s[:∂v0], :point]),  # hide\n            lengthscale=lengthscale, arrowsize=0.05, shininess=0.0,  # hide\n           color=edge_colors, diffuse=[0.0,0.0,0.0])  # hide\n  else  # hide\n    fig, ax, ob = mesh(new_m, color=vcat([[v,v,v] for v in tri_colors]...))  # hide\n     arrows!((s[s[:∂v0], :point] * (0.5 + lengthscale / 2)  # hide\n                    .+ s[s[:∂v1], :point] * (0.5 - lengthscale / 2)) ,  # hide\n             (s[s[:∂v1], :point] .- s[s[:∂v0], :point]),  # hide\n            lengthscale=lengthscale, arrowsize=0.05, shininess=0.0,  # hide\n           color=edge_colors, diffuse=[0.0,0.0,0.0])  # hide\n  end  # hide\n  if dim == 2  # hide\n      # hidespines!(ax); hidedecorations!(ax)  # hide\n      ax.aspect = AxisAspect(1.0) # Remove this line if 3D embedding  # hide\n  end  # hide\n  fig  # hide\nend # hide\n\n\nquad_coords = [(0,1,0), (1,1,0), (0,0,0),(1,0,0)] # hide\nplot_sset(quadrangle, quad_coords) # hide","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"There is no difference in methodology from the case of graphs, despite the different schema: we provide an instance of the datatype to serve as our pattern for replacement (such as the quadrangle above) and then need an instance to serve as our non-deleted subset of that pattern.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"L = quadrangle\nI = @acset SSet begin\n  E=4; V=4\n  src=[1,1,2,3]\n  tgt=[2,3,4,4]\nend\nquad_coords = [(0,1,0), (1,1,0), (0,0,0),(1,0,0)] # hide\nplot_sset(I, quad_coords) #","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"Our replacement pattern will add two triangles and an edge, but now the edge is perpendicular to where it was before.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"R = @acset SSet begin\n  T=2; E=5; V=4\n  d1=[2,3]; d2=[1,5]; d3=[5,4]\n  src=[1,1,2,3,2]\n  tgt=[2,3,4,4,3]\nend\nquad_coords = [(0,1,0), (1,1,0), (0,0,0),(1,0,0)] # hide\nplot_sset(R, quad_coords) # hide","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"Again we create a rewrite rule by relating the I to L and R.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"r = Rule(hom(I, R; monic=true),\n         hom(I, L; monic=true);\n         monic=true)","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"We can construct a mesh to test this rewrite on by gluing together two quadrilaterals via apushout along a common edge.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"edge = @acset SSet begin E=1; V=2; src=[1]; tgt=[2] end\nedge_left = hom(edge, L; initial=Dict([:V=>[1,3]]))\nedge_right = hom(edge, L; initial=Dict([:V=>[2,4]]))\nG = apex(pushout(edge_left, edge_right))\nsix_coords = vcat(quad_coords,[(-1.,1.,0.),(-1.,0.,0.),]) # hide\nplot_sset(G, six_coords) # hide\n","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"We then can perform the rewrite in larger contexts than just the pattern, such as a mesh with two quadrilaterals.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"res = rewrite(r, G)\nplot_sset(res, six_coords) # hide","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"(Image: Alt Text)","category":"page"},{"location":"#Applied-example:-Lotka-Volterra-agent-based-model","page":"AlgebraicRewriting.jl","title":"Applied example: Lotka-Volterra agent-based model","text":"","category":"section"},{"location":"#Overview","page":"AlgebraicRewriting.jl","title":"Overview","text":"","category":"section"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"The aim to recapture the dynamics of NetLogo's Wolf Sheep predation model in terms of declarative rewrite rules, rather than standard code-based interfaced. This models wolves in sheeps living in a periodic 2D space, which is also covered by grass. Wolves eat sheep to gain energy, sheep eat grass to gain energy, and grass takes time to grow back after it has been eaten. Each wolf/sheep has a direction and is moving in that direction (veering left or right randomly with some probability). At some rate, wolves/sheep undergo mitosis and their energy is split in half. As the wolves/sheep move, they lose energy, and they die if they are eaten or run out of energy. The simulation could go on indefinitely, or it could be ended when one of the two species completely dies out.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"The main difference with our reconstruction of the NetLogo model is that we model the 2D space as a discrete grid. This is more amenable to the style of pattern matching characteristic of AlgebraicRewriting, in contrast to floating point coordinates and collision checking to see when two entities occupy the same space.","category":"page"},{"location":"#Defining-the-datatype-we-are-rewriting","page":"AlgebraicRewriting.jl","title":"Defining the datatype we are rewriting","text":"","category":"section"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"using Catlab.Graphs.BasicGraphs: HasGraph # hide\n@present TheoryLV <: TheoryGraph begin # inherit Graph schema\n  (Sheep,Wolf,Grass)::Ob               # three more types of entities\n  (Dir, GrassVal, Eng)::AttrType       # three more types of attributes\n  sheep_loc::Hom(Sheep, E)             # sheep live on edges\n  wolf_loc::Hom(Wolf, E)               # wolves live on edges\n  grass::Hom(Grass, V)                 # grass lives on vertices\n  grassval::Attr(Grass,GrassVal)       # grass has an attribute\n  dir::Attr(E, Dir)                    # edges have an attributes\n  sheep_eng::Attr(Sheep, Eng)          # sheep have an attributes\n  wolf_eng::Attr(Wolf, Eng)            # wolves have an attribute\nend\n\n@acset_type LV_Generic(TheoryLV) <: HasGraph  # inherit Graph API\nconst LV = LV_Generic{Union{Var,Expr,Symbol}, # Dir\n                      Union{Var,Expr,Int},    # GrassVal\n                      Union{Var,Expr,Int}};   # Eng","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"grassval == 0 means alive grass; grassval > 0 represents the time","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"until the grass is alive.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"Sheeps and wolves have position and direction, so we assign each an edge.\nWe assume a convention where the vertex of a sheep/wolf is the edge source.\nDir is an attribute which can take values N, E, W, and S.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"There is a certain symmetry between wolves and sheep in the schema, which we can make explicit with the following endofunctor:","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"F = FinFunctor(\n  Dict([:Sheep => :Wolf, :Wolf => :Sheep, :Grass => :Grass, :V=>:V, :E=>:E,\n        :Dir=>:Dir, :GrassVal=>:GrassVal, :Eng=>:Eng]),\n  Dict([:sheep_loc=>:wolf_loc, :wolf_loc=>:sheep_loc,\n        :sheep_eng=>:wolf_eng, :wolf_eng=>:sheep_eng,\n        :src=>:src,:tgt=>:tgt,:dir=>:dir,\n        :grassval=>:grassval,:grass=>:grass]),\n  TheoryLV, TheoryLV\n);","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"We can apply F to a rewrite rule defined for sheep (e.g. that one dies when it has zero energy) and obtain the analogous rule for wolves without any effort.","category":"page"},{"location":"#Rules-and-Schedules","page":"AlgebraicRewriting.jl","title":"Rules and Schedules","text":"","category":"section"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"We can declare a Rule and how we wish to schedule that rule. The 'outer loop' is a WhileSchedule that executes all the rules in some order (i.e. a LinearSchedule wrapped around a list called seq made up of individual RuleSchedules).","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"extinct(prev, curr) = nparts(curr, :Wolf) == 0 || nparts(curr, :Sheep) == 0\noverall = WhileSchedule(ListSchedule(seq), :main, extinct, 10);","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"Let's show some of the things that went into seq. Below we define sheep reproduction to occur with probability 0.04 and wolf reproduction to occur with probability 0.05.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"using Catlab.Graphics.Graphviz: Attributes, Statement, Node # hide\nusing Catlab.Graphics.Graphviz # hide\n\n\nsupscript_d = Dict(['1'=>'¹', '2'=>'²', '3'=>'³', '4'=>'⁴', '5'=>'⁵', # hide\n                    '6'=>'⁶', '7'=>'⁷', '8'=>'⁸', '9'=>'⁹', '0'=>'⁰']) # hide\nsupscript(x::String) = join([get(supscript_d, c, c) for c in x]) # hide\nfunction Graph(p::LV,positions; name=\"G\", prog=\"neato\", title=\"\") # hide\n  pstr = [\"$(i),$(j)!\" for (i,j) in positions] # hide\n  stmts = Statement[] # hide\n    for s in 1:nv(p) # hide\n        vx, vy = positions[s] # hide\n        if !isempty(incident(p, s, :grass)) # hide\n          gv = p[only(incident(p, s, :grass)), :grassval] # hide\n        else # hide\n          gv = 0 # hide\n        end # hide\n        col = gv  == 0 ? \"lightgreen\" : \"tan\" # hide\n        push!(stmts,Node(\"v$s\", Attributes( # hide\n                    :label=>gv == 0 ? \"\" : string(gv),  # hide\n                    :shape=>\"circle\", # hide\n                    :color=> col, :pos=>pstr[s]))) # hide\n    end # hide\n  d = Dict([:E=>(1,0),:N=>(0,1), :S=>(0,1),:W=>(-1,0),]) # hide\n  for e in edges(p) # hide\n    s, t = src(p,e),tgt(p,e) # hide\n    dx, dy = get(d, p[e, :dir], (1,0)) # hide\n    (sx,sy), (tx,ty) = positions[s], positions[t] # hide\n\n    for (is_wolf, loc, eng) in [(:true,:wolf_loc,:wolf_eng), (false, :sheep_loc, :sheep_eng)] # hide\n        for w in incident(p, e, loc) # hide\n            L, R = 0.25, 0.2 # hide\n            wx = sx+L*dx+R*rand() # hide\n            wy = sy+L*dy+R*rand() # hide\n            ID = \"$(is_wolf ? :w : :s)$w\" # hide\n            append!(stmts,[Node(ID, Attributes( # hide\n                            :label=>\"$w\"*supscript(\"$(p[w,eng])\"), # hide\n                            :shape=>\"square\", :width=>\"0.3px\", :height=>\"0.3px\", :fixedsize=>\"true\", # hide\n                            :pos=>\"$(wx),$(wy)!\",:color=> is_wolf ? \"red\" : \"lightblue\")), # hide\n                           ]) # hide\n        end # hide\n    end # hide\n  end # hide\n  g = Graphviz.Digraph(name, Statement[stmts...]; prog=prog, # hide\n        graph_attrs=Attributes(:label=>title, :labelloc=>\"t\"), # hide\n        node_attrs=Attributes(:shape=>\"plain\", :style=>\"filled\")) # hide\n  return g # hide\nend # hide\n\ns_reprod_l =  @acset LV begin\n  Sheep=1; V=2; E=1; src=1;tgt=2; dir=[Var(:d)];\n  sheep_eng=[Var(:a)]; sheep_loc=1\nend\n\nGraph(s_reprod_l, [0=>0,0=>1]) # hide","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"This defines a pattern which we wish to match. The suffix _l indicates that this is the L of a rewrite rule, which is a partial map L → R, i.e. L ↩ I → R.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"We need to define the interface I, which contains the subobject of L which is not deleted.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"s_reprod_i = deepcopy(s_reprod_l); rem_part!(s_reprod_i, :Sheep, 1)","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"And the right object, R, includes things that are added. So we've removed a sheep with energy a at a certain position and replace it with two sheep with a/2 energy.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"s_reprod_r = deepcopy(s_reprod_i)\nadd_parts!(s_reprod_r, :Sheep, 2; sheep_loc=[1,1],\n           sheep_eng=[:(round(Int, a/2, RoundDown))])\nGraph(s_reprod_r, [0=>0,0=>1]) # hide","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"We assemble this data into a rewrite rule.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"sheep_reprod = Rule(hom(s_reprod_i,s_reprod_l),\n                    hom(s_reprod_i,s_reprod_r));","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"As mentioned before, we can turn this into a wolf reproduction rule by applying our functor. Then we add the two rules along with their probabilities. The false here refers to whether or not we apply the rule only once or whether we apply it for every match we find (which is what we want to do, to give each sheep a 4% chance of reproducing).","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"wolf_reprod = F(sheep_reprod)","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"append!(seq, [RuleSchedule(sheep_reprod,:sheep_reprod, false,0.04),\n              RuleSchedule(wolf_reprod, :wolf_reprod, false,0.05)]);","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"Note that our pattern L can have Var variables, and our right hand side R can have Julia expressions involving those variables.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"Another illustrative example is the 'move forward' rule. We simultaneously advance the sheep forward one space and decrement its energy by 1.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"s_move_forward_l = @acset LV begin\n  Sheep=1; V=3; E=2;\n  src=[1,2]; tgt=[2,3]; dir=[Var(:a), Var(:a)]\n  sheep_eng=[Var(:x)]; sheep_loc=1\nend\nGraph(s_move_forward_l, [0=>0,0=>1,0=>2]) # hide","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"This pattern has two contiguous edges that are in the same direction (implicitly constrainted by using Var(:a) twice) and the sheep in the first position.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"\ns_move_forward_i = deepcopy(s_move_forward_l)\nrem_part!(s_move_forward_i, :Sheep, 1)\n\ns_move_forward_r = deepcopy(s_move_forward_i)\nadd_part!(s_move_forward_r, :Sheep; sheep_loc=2, sheep_eng=:(x-1))\n\nGraph(s_move_forward_r, [0=>0,0=>1,0=>2]) # hide","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"We delete the sheep and recreate one in position #2, with one fewer energy. This is only valid though if the sheep has any energy. To prevent this rule from firing, we need a negative application condition. This embeds the pattern L in a larger context N that has the semantics of: if L and N are matched, then actually don't fire the rule. The pattern we want to avoid is one where the sheep has zero energy.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"zero_s = deepcopy(s_move_forward_l)\nset_subpart!(zero_s, :sheep_eng, 0)\nGraph(zero_s, [0=>0,0=>1,0=>2]) # hide","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"sheep_move_forward = Rule(hom(s_move_forward_i, s_move_forward_l),\n                          hom(s_move_forward_i, s_move_forward_r),\n                          [NAC(hom(s_move_forward_l,zero_s; bindvars=true))])\n\nwolf_move_forward = F(sheep_move_forward)","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"In all these cases, automatic homomorphism finding is sufficient for obtaining the morphism data of L ↩ I → R.","category":"page"},{"location":"#Other-functions","page":"AlgebraicRewriting.jl","title":"Other functions","text":"","category":"section"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"Functions to initialize and visualize the world-states are defined in the Jupyter notebook. Important functionality only possible in the notebook is the ability to move a slider and view the progression of a simulation.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"(Image: Alt Text)","category":"page"},{"location":"#Alternative-rewriting-semantics","page":"AlgebraicRewriting.jl","title":"Alternative rewriting semantics","text":"","category":"section"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"A nice property of DPO is that you can analyze the relationship between I and L to see exactly what will be deleted (likewise for I and R to see what will be added). However, this is sometimes not what we want: we wish to delete outside the context L, or to implicitly create things. The former is possible in single pushout rewriting, and both are possible in sesqui pushout rewriting.","category":"page"},{"location":"#Single-pushout-rewriting","page":"AlgebraicRewriting.jl","title":"Single pushout rewriting","text":"","category":"section"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"Implicit deletion works like a cascading delete: if you delete a vertex (for example), then you implicitly delete an edge which refers to that vertex (and a triangle that refers to that edge, and so on). Here we delete a triangle and a vertex explicitly, but implicitly the deleted vertex","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"Tri = @acset SSet begin\n    T=1; E=3; V=3;\n    d1=[1]; d2=[2]; d3=[3];\n    src=[1,1,2]; tgt=[3,2,3]\nend\nL = Tri\nr = Rule{:SPO}(homomorphisms(edge, L)[2],id(edge))\nm = homomorphism(L, quadrangle)\n# can_pushout_complement(r.L, m) == false\nrewrite_match(r,m)","category":"page"},{"location":"#Sesqui-pushout-rewriting","page":"AlgebraicRewriting.jl","title":"Sesqui pushout rewriting","text":"","category":"section"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"Here our rewrite rule takes a vertex and duplicates it.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"L = @acset SSet begin V=1 end\nI = @acset SSet begin V=2 end\nr=Rule{:SqPO}(homomorphism(I,L),id(I))","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"With sesqui-pushout semantics, when we apply this to the vertex of a triangle, this will create two triangles.","category":"page"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"G = Tri\nm = CSetTransformation(L, G, V=[1]);\nnparts(sesqui_pushout_rewrite(l, r, m), :T) == 4 || error(\"We get 4 'triangles' when we ignore equations\")\nrewrite_match(r, m; pres=ThSemisimplicialSet) # pass in the equations","category":"page"},{"location":"#Rewriting-things-that-aren't-C-Sets","page":"AlgebraicRewriting.jl","title":"Rewriting things that aren't C-Sets","text":"","category":"section"},{"location":"","page":"AlgebraicRewriting.jl","title":"AlgebraicRewriting.jl","text":"Anything that implements some basic features (e.g. pushout, pushout_complement) can be used with this rewriting infrastructure. Generally, constructions that are built on top of C-Sets","category":"page"},{"location":"#Slices","page":"AlgebraicRewriting.jl","title":"Slices","text":"","category":"section"},{"location":"#Structured-cospans","page":"AlgebraicRewriting.jl","title":"Structured cospans","text":"","category":"section"},{"location":"#Diagrams","page":"AlgebraicRewriting.jl","title":"Diagrams","text":"","category":"section"}]
}
