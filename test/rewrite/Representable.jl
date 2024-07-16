module TestRepresentable 

using Test, AlgebraicRewriting, DataMigrations, Catlab

yWG = yoneda_cache(WeightedGraph{Float64}; clear=true);


""" 
 w w   2.0
•→•→•  •→•  
"""

@migration(SchWeightedGraph, begin
  I => @join begin
    v::V
    (e1,e2)::E
    weight(e1) == weight(e2) 
  end
end) |> (f->ob_map(colimit_representables(f, yWG), :I))


"""↻•↺  <= • => •→• """
d = @migration(SchRuler,SchWeightedGraph, begin
    L => @join begin
      (e1,e2)::E
      src(e1) == tgt(e1)
      src(e2) == tgt(e2)
      src(e2) == tgt(e1)      
    end
    K => @join begin v::V end 
    R => @join begin e::E end 

    r => begin 
      v => src(e)
    end
end)

r = Rule(d, yWG; semantics=:SPO, expr=(Weight=[vs->0.],), monic=true)

G = path_graph(WeightedGraph{Float64}, 2)
add_edges!(G, [2,2], [2,2])
G[:weight] = [-1.,10,10]
m = get_matches(r, G)[1]
expected = @acset WeightedGraph{Float64} begin 
  V=3; E=2; src=[1,2]; tgt=[2,3]; weight=[-1.,0.] 
end
@test is_isomorphic(rewrite_match(r, m), expected)

end # module 
