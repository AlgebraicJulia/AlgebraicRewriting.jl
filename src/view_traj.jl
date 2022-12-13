using .Interact

using Catlab.WiringDiagrams, Catlab.Graphics
using Catlab.WiringDiagrams.DirectedWiringDiagrams: out_port_id
using Catlab.Graphics.Graphviz: Graph, Subgraph, Statement, pprint, Node, Edge, NodeID
using .Schedules: color 

# Code related to combining two graphs together. Potentially upstreamable.
##########################################################################
to_subgraph(g::Graph) = Subgraph(
  name="cluster_"*g.name, stmts=g.stmts, 
  graph_attrs=g.graph_attrs, node_attrs=g.node_attrs, edge_attrs=g.edge_attrs)


rename(g::Graph, suffix::String) = Graph(
  g.name * suffix, g.directed, g.prog,
  [rename(stmt, suffix) for stmt in g.stmts],
  g.graph_attrs, g.node_attrs,g.edge_attrs, 
)

rename(n::Node, suffix::String) = Node(n.name*suffix; n.attrs...)
rename(n::Edge, suffix::String) = Edge([rename(i,suffix) for i in n.path]; n.attrs...)
rename(n::NodeID, suffix::String) = NodeID(n.name*suffix, n.port, n.anchor)
mrg(g1::Graph,g2::Graph; kw...) =  
  Graph(name="Trajectory",directed=g1.directed, prog=g1.prog,
        stmts=Statement[to_subgraph(g1),to_subgraph(rename(g2,"suffix"))]; kw...)

# Visualization
###############
"""
Visualize a trajectory with two views: one showing the current position within 
the schedule, and the other showing the world state.
"""
function view_traj(sched_::WiringDiagram, rG::Traj, viewer; 
                   positions=nothing)
  sched = WiringDiagram([], [])
  copy_parts!(sched.diagram,sched_.diagram)

  positions_cache = Vector{Any}(fill(nothing, length(rG)))
  positions_cache[1] = positions

  # Push forward previous positions along partial map if current ones unknown
  # This is really hard to do in a satisfying way.
  function get_positions(i)
    if      isnothing(positions)          return nothing
    elseif !isnothing(positions_cache[i]) return positions_cache[i]
    end
    old_pos, morph = get_positions(i-1), rG[i]
    pos = Vector{Any}(fill(nothing, nv(rG[i].G)))
    l, r = rG[i].pmap
    for (v, lv) in enumerate(collect(l[:V]))
      pos[r[:V](v)] = old_pos[lv]
    end
    return positions_cache[i] = pos
  end

  # Create slider 
  return @manipulate for n in slider(1:length(rG), value=1, label="Step:")
    step = rG[n]
    name, G = step.desc, codom(step.world)
    rhs_graph = nothing 
    try # feed in positions, if function expects this
      rhs_graph = viewer(G; positions=get_positions(n)) 
    catch _
      rhs_graph = viewer(G)
    end 
    begin # mark position in schedule 
      sched.diagram[:outer_in_port_type] = [""]
      sched.diagram[:outer_out_port_type] = [""]
      sched.diagram[:out_port_type] = fill("", nparts(sched.diagram, :OutPort))
      if step.inwire.source.box == input_id(sched) 
        sched.diagram[step.inwire.source.port, :outer_in_port_type] = "→"
      else 
        sched.diagram[out_port_id(sched, step.inwire.source), :out_port_type] = "→"
      end
      sched.diagram[out_port_id(sched, step.outwire.source), :out_port_type] = "←"
    end

    lhs_graph = to_graphviz(sched; labels=true, 
      graph_attrs=Dict(:label=>name, :labelloc=>"t"),
      node_colors=Dict(i=>color(b.value) for (i,b) in enumerate(boxes(sched))))

    merged_graph = mrg(lhs_graph,rhs_graph)
    # pprint(merged_graph)
    return merged_graph
  end
end
