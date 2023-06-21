module AlgebraicRewritingLuxorExt 
using AlgebraicRewriting
using Catlab.WiringDiagrams, Catlab.Graphics, Catlab.CategoricalAlgebra
using Catlab.Graphics.Graphviz: Graph, Subgraph, Statement, pprint, Node, Edge, NodeID
using AlgebraicRewriting.Wiring: color 
using Luxor

# Visualization
###############
"""
Visualize a trajectory with two views: one showing the current position within 
the schedule, and the other showing the world state.

Viewer must be a function which accepts a path and writes an image to it.
"""
function AlgebraicRewriting.view_traj(sched_::Schedule, rG::Sim, viewer; 
                                      out="traj", agent=false, names=nothing)
  if isdir(out) # clear old dir
    for fi in filter(x->length(x)>4 && x[end-3:end] == ".png",  readdir(out))
      rm(joinpath(out,fi))
    end
  else
    mkdir(out)
  end
  for n in 1:length(rG)-1
    view_traj(sched_,rG, viewer, n; out=out, agent=agent,names=names)
  end
end

"""
If `agent` is true, then the viewer function should operate on 
ACSetTransformations, rather than ACSets.
"""
function view_traj(sched_::Schedule, rG::Sim, viewer, n::Int; out="traj", agent=false, names=nothing)
  traj = last(rG).edge.o.val
  length(traj)+1 == length(rG) || error("Traj length doesn't match sim length")
  step = rG[n+1]

  f = tempname()
  sched = view_sched(sched_; name=step.desc, source=step.inwire.source, 
                     target=step.outwire.source, names=names)
  open(f, "w") do io
    show(io,"image/svg+xml",sched)
  end
  svgs = Any[readsvg(f)]

  start_world = n==1 ? traj.initial : traj[n-1].world
  end_world = traj[n].world
  for g in (agent ? identity : codom).([start_world, end_world])
    f = tempname()
    viewer(g, f) # write graph to file
    img = 1
    try 
      img = readsvg(f)
    catch _
      str = read(f, String)
      img = @drawsvg begin 
        background("white")
        settext(str; markup=false)
      end
      
    end 
    push!(svgs, img) # TODO replace this to work with png and ASCII
  end
  # Constants
  SPACE = 10
  heights=[x.height for x in svgs]; width=maximum([x.width for x in svgs])
  height=sum(heights)
  # Helper functions
  p(h) = Point(width/2,h)
  hline(h) = line(Point(0,h),Point(width,h), :stroke)
  pimg(i,h) = placeimage(svgs[i],p(h); centered=true)
  # Draw image 
  Drawing(width, height+SPACE*2, "$out/$n.png")
  pimg(1,heights[1]/2)
  hline(heights[1])
  pimg(2,heights[1] + SPACE + heights[2]/2)
  hline(sum(heights[1:2])+SPACE)
  pimg(3,2*SPACE + height - heights[3]/2)
  finish()
end

end # module 
