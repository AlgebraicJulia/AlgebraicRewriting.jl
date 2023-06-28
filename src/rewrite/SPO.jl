module SPO 

using Catlab, Catlab.CategoricalAlgebra

using ...CategoricalAlgebra.CSets: var_pullback, cascade_subobj
using ..Utils
import ..Utils: rewrite_match_maps


# Single-pushout rewriting
##########################

function rewrite_match_maps(r::Rule{:SPO}, m)
  e = "SPO rule is not a partial morphism. Left leg not monic."
  is_monic(r.L) || error(e)
  (rmono, rmap),(gmono, gmap)  = partial_pushout(Span(r.L, r.R), Span(id(dom(m)), m))
  return Dict(:rmono=>rmono, :rmap=>rmap, :gmono=>gmono, :gmap=>gmap)
end


"""
C ← Ag ↪ A ↩ Af → B 
   
A ↩ f∇g → Bgf ↪ B 
     ↓   ⌜ ↓
C ↩ Cfg -> D

Implementation of Construction 6 in Löwe's 
"Algebraic approach to SPO graph transformation"
"""
function partial_pushout(f::Span, g::Span)
  AfA, AfB = f
  AgA, AgC = g 
  A, B, A_, C = codom.([AfA, AfB, AgA, AgC])
  A == A_ || error("f and g do not share common domain")
  all(is_monic, [AfA, AgA]) || error("f and g must be *partial* maps")
  S = acset_schema(A)
  ι(o) = (o ∈ ob(S) ? identity : AttrVar)
  κ(o) = vs -> o ∈ ob(S) ? vs : Set([v.val for v in vs if v isa AttrVar])
  # Create f ∇ g 
  #-------------
  # Step 1: compute Af ∩ Ag
  glue = Dict{Symbol,Set{Int}}(map(types(S)) do o 
    o => κ(o)(intersect(Set.(collect.([AfA[o],AgA[o]]))...))
  end)

  # Step 2: add any elements which are mapped to the same elems by f or g 
  for (mono,ϕ) in [f,g]
    for o in types(S)
      xs = vcat(Vector{Int}[preimage(mono[o],go) for go in glue[o]]...)
      glue_img = Set(ϕ[o].(ι(o).(xs)))
      for i in parts(dom(ϕ),o)
        if ϕ[o](ι(o)(i)) ∈ glue_img
          push!(glue[o],mono[o](i)) 
        end 
      end
    end 
  end
  comps = NamedTuple(Dict([k=>collect(v) for (k,v) in collect(glue)]))
  fg_A = Subobject(A, comps) |> hom # f ∇ g ↪ A
  fg = dom(fg_A) # f ∇ g
  # Construct scopes Bgf ⊆ B and Cfg ⊆ C
  #---------------------------
  Bgf_B, Cfg_C = map([f,g]) do (mono, ϕ) 
    sub = Dict{Symbol,Vector{Int}}(map(types(S)) do o 
      x1 = setdiff(parts(codom(ϕ),o),collect(ϕ[o])) # e.g. C - g(A)
      pre = [preimage(mono[o], fg_A[o](i)) for i in parts(fg,o)]
      x2 = Set(collect(ϕ[o].(vcat(pre...))))  # e.g. g(f ∇ g)
      o => sort(collect(x1 ∪ x2))
    end)

    hom(Subobject(codom(ϕ), NamedTuple(cascade_subobj(codom(ϕ), sub))))
  end
  codom(Cfg_C) == C || error("Not C ")
  codom(Bgf_B) == B || error("Not B ") 
  Cfg, Bgf = dom.([Cfg_C,Bgf_B])
  fg_Bgf, fg_Cfg = map(zip([f,g], [Bgf_B, Cfg_C])) do ((mono, ϕ),cod)
    
    init = Dict(map(ob(S)) do o 
      o => map(parts(fg, o)) do i 
        c_index = ϕ[o](only(preimage(mono[o],fg_A[o](i))))
        return findfirst(==(c_index), collect(cod[o]))
      end
    end)
    only(homomorphisms(fg, dom(cod); initial=init))
  end

  Bd,Cd = pushout(fg_Bgf,fg_Cfg)
  dom(Bd) == Bgf || error("bad dom1")
  dom(Cd) == Cfg || error("bad dom2")
  return Span(Bgf_B,Bd), Span(Cfg_C,Cd)
end


end # module 
