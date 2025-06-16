module Processes 
export find_deps 

using Catlab
using Catlab.Theories: ⋅

using ..Rewrite.Utils

# Dependency analysis via Graph Processes
#####################
"""
The relevant maps of an application of a single DPO rewrite.
"""
struct RWStep
  rule
  g
  match
  comatch
  function RWStep(r,g,m,c::T) where {T<:ACSetTransformation}
    codom(left(r)) == dom(m) || error("left(r)!=dom(m)")
    codom(right(r)) == dom(c) || error("right(r)!=dom(c)")
    codom(m) == codom(left(g)) || error("codom(m)!=codom(l)")
    codom(c) == codom(right(g)) || error("codom(c)!=codom(r)")
    new(r,g,m,c)
  end
end

"""Convert a vector of rewrite rule followed by match morphism to RWSteps"""
function rw_steps(steps::AbstractVector; cat)
  map(steps) do (r, m)
    d = rewrite_match_maps(r, m; cat)
    RWStep(Span(r.L, r.R), Span(d[:kg], d[:kh]), m, d[:rh])
  end
end

"""
For a concrete sequence of rewrites applications [a₁,a₂...aₙ], compute a poset
on the set of applications which reflects their casual connections, where a < b
mean that a must occur temporaly before b.
"""
function find_deps(seq::Vector{RWStep}; cat)
  # Construct a diagram which identifies parts across different rewrite steps
  n   = length(seq)
  ob₁ = [apex(s.g) for s in seq];
  ob₂ = codom.([left(first(seq).g), right.([x.g for x in seq])...])
  hom = vcat([[left(s.g), right(s.g)] for s in seq]...)
  src = vcat([fill(i,2) for i in 1:n]...); # [1, 1, 2, 2, 3, 3, ..., n, n]
  tgt = [1,vcat([fill(i,2) for i in 2:n]...)...,n+1] # [1, 2, 2, ..., n, n, n+1]
  hs  = collect(zip(hom, src, tgt))
  clim = colimit[cat](BipartiteFreeDiagram(ob₁, ob₂, hs))
  clegs = legs(clim)

  # Identify which things are preserved, deleted, and created for each part
  Ob = objects(acset_schema(first(ob₁))) # objects in the schema 
  pres, del, cre = [Dict() for _ in 1:3]
  for o in Ob 
    pres[o], del[o], cre[o] = [[] for _ in 1:3]
    img(f) = Set(collect(f[o])) # the image of a map
    for (i,s) in enumerate(seq)
      push!(pres[o], @withmodel cat (⋅) begin 
        img(left(s.rule) ⋅ s.match ⋅ clegs[i])
      end)
      push!(del[o], setdiff(img(compose[cat](s.match, clegs[i])), pres[o][end]))
      push!(cre[o], setdiff(img(compose[cat](s.comatch, clegs[i+1])), pres[o][end]))
    end
  end 

  # Use the above to compute a presentation of a poset
  deps = Graph(length(seq))
  for o in Ob 
    for i in 1:n
      cre_i = cre[o][i]
      for j in filter(j->j!=i, 1:n)
        pres_del_j = pres[o][j] ∪ del[o][j]
        if !isempty(cre_i ∩ pres_del_j) && isempty(edges(deps, i, j))
          add_edge!(deps, i, j)
        end
      end
    end
  end
  return deps 
end

find_deps(s::AbstractVector; cat) = find_deps(rw_steps(s; cat); cat)

end # module 
