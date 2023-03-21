module SPO 

using Catlab, Catlab.CategoricalAlgebra

using ...CategoricalAlgebra.CSets: var_pullback
using ..Utils
import ..Utils: rewrite_match_maps


# Single-pushout rewriting
##########################

"""
  f         f
A ↣ B     A ↣ B
    ↓ g   ↓   ↓ g
    C     D ↣ C

Pullback complement where there first morphism is a mono.

Define D to be Im(g) to make it the largest possible subset of C such that we
can get a pullback.
"""
function pullback_complement(f::ACSetTransformation, g; check=false)
  is_monic(f) || error("can only take pullback complement if f is mono")
  A = dom(f)
  S = acset_schema(A)
  d_to_c = hom(¬g(¬f(A))) # why isn't this just g(B)?
  # force square to commute by looking for the index in D making it commute
  D = dom(d_to_c)

  # big hacks in order to make attribute variables work 
  for at in attrtypes(S)
    attrvals = vcat([D[a] for a in attrs(S; to=at, just_names=true)]...)
    vars = [v.val for v in sort(collect(filter(x->x isa AttrVar, attrvals)))]
    add_parts!(D, at, length(vars))
    for a in attrs(S; to=at, just_names=true)
      for (i,v) in enumerate(D[a])
        if v isa AttrVar 
          D[i,a] = AttrVar(findfirst(==(v.val), vars))
        end 
      end
    end
  end
  d_to_c = homomorphism(D, codom(d_to_c); 
                        initial=Dict(o=>collect(d_to_c[o]) for o in ob(S)))
  
  fg = compose(f,g)
  ad = Dict(map(ob(S)) do cmp 
    fg_as = fg[cmp]
    cmp => Vector{Int}(map(collect(fg_as)) do fg_a
      findfirst(==(fg_a), collect(d_to_c[cmp]))
    end)
  end)
  a_to_d = homomorphism(A, dom(d_to_c); initial=ad) 

  !check || is_natural(d_to_c) || error("d_to_c ")
  !check || is_natural(a_to_d) || error("a_to_d ")
  return a_to_d => d_to_c
end

"""    rewrite_match_maps(r::Rule{:SPO}, ac)
NOTE: In the following diagram, a double arrow indicates a monic arrow.

We start with two partial morphisms, construct M by pullback, then N & O by
pullback complement, then finally D by pushout.


A ⇇ K → B         A ⇇ K → B
⇈                 ⇈ ⌟ ⇈ ⌞ ⇈
L          ⭆      L ⇇ M → N
↓                 ↓ ⌞ ↓ ⌜ ↓
C                 C ⇇ O → D

We assume the input A→C is total, whereas A→B may be partial, so it is given
as a monic K↣A and K→B.

Specified in Fig 6 of:
"Graph rewriting in some categories of partial morphisms"
"""
function rewrite_match_maps(r::Rule{:SPO}, ac)
  ka, kb = r.L, r.R
  e = "SPO rule is not a partial morphism. Left leg not monic."
  is_monic(ka) || error(e)

  lc, la = ac, id(dom(ac))
  ml, mk = var_pullback(Cospan(la, ka))
  mn, nb = pullback_complement(mk, kb)
  mo, oc = pullback_complement(ml, lc)
  od, nd = pushout(mo, mn)
  return Dict(:ml=>ml, :mk=>mk, :mn=>mn, :mo=>mo, :nb=>nb, :oc=>oc, 
              :nd=>nd, :od=>od)
end


end # module 
