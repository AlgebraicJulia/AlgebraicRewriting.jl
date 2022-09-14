
using Catlab, Catlab.Graphs, Catlab.CategoricalAlgebra
using CairoMakie, GeometryBasics
using Base.Iterators
using CombinatorialSpaces
import AlgebraicPetri
using CombinatorialSpaces.SimplicialSets: get_edge!

"""
Suppose we want to perform rewriting on a mesh with triangles defined over
certain triples of edges.
"""

@present ThSemisimplicialSet  <: SchGraph begin
  T :: Ob
  (d1,d2,d3)::Hom(T,E)
  compose(d1, src) == compose(d2, src)
  compose(d1, tgt) == compose(d3, tgt)
  compose(d2, tgt) == compose(d3, src)
end
@acset_type SSet(ThSemisimplicialSet)

quadrangle = @acset SSet begin
    T=2; E=5; V=4
    d1=[1,1]; d2=[2,3]; d3=[4,5]
    src=[1,1,1,2,3]
    tgt=[4,2,3,4,4]
end

function plot_sset(ss::SSet, points::Vector,
                   tri_colors::Union{Nothing,Vector}=nothing)
    dflt = collect(take(cycle([:blue,:red,:green, :purple, :pink, :yellow,
                               :grey, :orange, :brown, :cyan]),
                        nparts(ss, :T)))
    tri_colors = isnothing(tri_colors) ? dflt : tri_colors
    # Validate inputs
    lengthscale=0.8
    dim = length(points[1])
    length(points) == nparts(ss,:V) || error("# of points")
    if dim == 2
        points = [(p1,p2,0.) for (p1,p2) in points]
    elseif dim != 3
        error("dim $dim")
    end
    tri_colors = tri_colors[1:nparts(ss, :T)]

    # Convert SSet to EmbeddedDeltaSet2D
    s = EmbeddedDeltaSet2D{Bool, Point{3, Float64}}()

    edge_colors = [:black for _ in nparts(ss, :E)]
    add_vertices!(s, length(points), point=points)
    for (src, tgt) in zip(ss[:src], ss[:tgt])
        get_edge!(s, src, tgt)
    end

    for t in parts(ss,:T)
    glue_sorted_triangle!(s, ss[t,[:d1,:src]],
                             ss[t,[:d3,:src]],
                             ss[t, [:d1,:tgt]])
    end

    # Split mesh into component triangles
  m = GeometryBasics.Mesh(s)
  x = faces(m)
  m_points = m.position[vcat([[t[1],t[2],t[3]] for t in x]...)]
  m_faces = TriangleFace{Int}[[((t-1) * 3) .+ (1,2,3) for t in  1:length(x)]...]
  new_m = GeometryBasics.Mesh(Point{3, Float64}[m_points...], m_faces)
  if ntriangles(s) == 0
     fig, ax, ob = arrows((s[s[:∂v0], :point] * (0.5 + lengthscale / 2)
                            .+ s[s[:∂v1], :point] * (0.5 - lengthscale / 2)) ,
                          (s[s[:∂v1], :point] .- s[s[:∂v0], :point]),
            lengthscale=lengthscale, arrowsize=0.05, shininess=0.0,
           color=edge_colors, diffuse=[0.0,0.0,0.0])
  else
    fig, ax, ob = mesh(new_m, color=vcat([[v,v,v] for v in tri_colors]...))
     arrows!((s[s[:∂v0], :point] * (0.5 + lengthscale / 2)
                    .+ s[s[:∂v1], :point] * (0.5 - lengthscale / 2)) ,
             (s[s[:∂v1], :point] .- s[s[:∂v0], :point]),
            lengthscale=lengthscale, arrowsize=0.05, shininess=0.0,
           color=edge_colors, diffuse=[0.0,0.0,0.0])
  end
  if dim == 2
      spines!(ax); hidedecorations!(ax)
      ax.aspect = AxisAspect(1.0) # Remove this line if 3D embedding
  end
  fig
end


quad_coords = [(0,1,0), (1,1,0), (0,0,0),(1,0,0)]
plot_sset(quadrangle, quad_coords)



L = quadrangle
I = @acset SSet begin
  E=4; V=4
  src=[1,1,2,3]
  tgt=[2,3,4,4]
end
quad_coords = [(0,1,0), (1,1,0), (0,0,0),(1,0,0)]
plot_sset(I, quad_coords)


"""
Our replacement pattern will add two triangles and an edge, but now the edge
is perpendicular to where it was before.
"""

R = @acset SSet begin
  T=2; E=5; V=4
  d1=[2,3]; d2=[1,5]; d3=[5,4]
  src=[1,1,2,3,2]
  tgt=[2,3,4,4,3]
end
quad_coords = [(0,1,0), (1,1,0), (0,0,0),(1,0,0)]
plot_sset(R, quad_coords)


"""
Again we create a rewrite rule by relating the `I` to `L` and `R`.
"""

r = Rule(hom(I, R; monic=true),
         hom(I, L; monic=true);
         monic=true)


"""
We can construct a mesh to test this rewrite on by gluing together two
quadrilaterals (via a *pushout* along a common edge).
"""

edge = @acset SSet begin E=1; V=2; src=[1]; tgt=[2] end
edge_left = hom(edge, L; initial=Dict([:V=>[1,3]]))
edge_right = hom(edge, L; initial=Dict([:V=>[2,4]]))
G = pushout(edge_left, edge_right) |> apex
six_coords = vcat(quad_coords,[(-1.,1.,0.),(-1.,0.,0.),])
plot_sset(G, six_coords)

"""
We then can perform the rewrite in larger contexts than just the pattern, such
as a mesh with two quadrilaterals.
"""
res = rewrite(r, G)



"""
### Single pushout rewriting
Implicit deletion works like a cascading delete: if you delete a vertex
(for example), then you implicitly delete an edge which refers to that vertex
(and a triangle that refers to that edge, and so on). Here we delete a triangle
and a vertex explicitly, but implicitly the deleted vertex
"""

Tri = @acset SSet begin
    T=1; E=3; V=3;
    d1=[1]; d2=[2]; d3=[3];
    src=[1,1,2]; tgt=[3,2,3]
end
L = Tri
r = Rule{:SPO}(homomorphisms(edge, L)[2],id(edge))
m = homomorphism(L, quadrangle)
# can_pushout_complement(r.L, m) == false
rewrite_match(r,m)

"""
Sesqui pushout rewriting

Here our rewrite rule takes a vertex and duplicates it.
"""
L = @acset SSet begin V=1 end
I = @acset SSet begin V=2 end
r=Rule{:SqPO}(homomorphism(I,L),id(I))

"""
With sesqui-pushout semantics, when we apply this to the vertex of a triangle,
this will create two triangles.
"""
G = Tri
m = CSetTransformation(L, G, V=[1]);
nparts(sesqui_pushout_rewrite(l, r, m), :T) == 4 || error("We get 4 'triangles' when we ignore equations")
rewrite_match(r, m; pres=ThSemisimplicialSet) # pass in the equations
