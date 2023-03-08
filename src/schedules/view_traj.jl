using Catlab.WiringDiagrams, Catlab.Graphics
using Catlab.Graphics.Graphviz: Graph, Subgraph, Statement, pprint, Node, Edge, NodeID
using .Wiring: color 
using .Luxor

# Visualization
###############
"""
Visualize a trajectory with two views: one showing the current position within 
the schedule, and the other showing the world state.
"""
function view_traj(sched_::WiringDiagram, rG::Traj, viewer; out="traj")
  if isdir(out) # clear old dir
    for fi in filter(x->length(x)>4 && x[end-3:end] == ".png",  readdir(out))
      rm(joinpath(out,fi))
    end
  else
    mkdir(out)
  end
  for n in 1:length(rG)
    view_traj(sched_,rG, viewer, n; out=out)
  end
end 

function view_traj(sched_::WiringDiagram, rG::Traj, viewer, n::Int; out="traj")
  step = rG[n]
  graphs = [view_sched(sched_; name=step.desc, source=step.inwire.source, 
                       target=step.outwire.source)]
  worlds = [(n==1 ? rG.initial : rG[n-1].world), step.world]
  append!(graphs, viewer.(codom.(worlds)))
  svgs = map(enumerate(graphs)) do (i,g)
    open("tmp$i.svg", "w") do io 
      show(io,"image/svg+xml",g)
    end
    readsvg("tmp$i.svg")
  end
  for i in 1:3 rm("tmp$i.svg") end

  heights=[x.height for x in svgs]; width=maximum([x.width for x in svgs])
  height=sum(heights)
  Drawing(width+10, height+10, "$out/$n.png")
  p(h) = Point(width/2,h)
  line(Point(0,heights[1]),Point(width,heights[1]), :stroke)
  line(Point(0,sum(heights[1:2])),Point(width,sum(heights[1:2])), :stroke)
  placeimage(svgs[1],p(heights[1]/2); centered=true)
  placeimage(svgs[2],p(heights[1] + heights[2]/2); centered=true)
  placeimage(svgs[3],p(height - heights[3]/2); centered=true)
  finish()
end



