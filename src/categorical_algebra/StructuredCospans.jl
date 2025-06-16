module StructuredCospans

export StructuredMultiCospanHom, StructuredMulticospan, openrule, can_open_pushout_complement, open_rewrite, open_rewrite_match, idH_, idV_, composeV_, composeH_, id2_, id2V_, id2H_

using Catlab, Catlab.CategoricalAlgebra, Catlab.Theories
import Catlab.Theories: dom, codom, compose, ⋅, id
import Catlab.CategoricalAlgebra: homomorphisms
using ..CSets

# Maps between structured multicospans
######################################
"""
A component-wise map between two cospans. The first component given is the apex
map, with the following maps being the legs.
"""
struct StructuredMultiCospanHom{L}
  src::StructuredMulticospan{L}
  tgt::StructuredMulticospan{L}
  maps::Vector{<:ACSetTransformation} # one for each leg, plus apex
  function StructuredMultiCospanHom(s::StructuredMulticospan{L},
    t::StructuredMulticospan{L}, m::Vector{<:ACSetTransformation}) where {L}
    length(m) == length(legs(s)) + 1 || error("bad # maps")
    length(m) == length(legs(t)) + 1 || error("bad # maps")
    𝒞 = get_ACS(L)
    ⋅(a,b) = force(compose[𝒞](a,b))
    eq(f) = (dom(f), codom(f), [k=>collect(v) for (k,v) in pairs(components(f))])
    for (i,(s_leg, t_leg, st_map)) in enumerate(zip(legs(s), legs(t), m[2:end]))
      ms, mt = force(s_leg ⋅ m[1]), force(st_map ⋅ t_leg)
      dom(ms) == dom(mt) || error("domain error $(dom(ms)) $(dom(mt))")
      codom(ms) == codom(mt) || error("codomain error $(codom(ms)) $(codom(mt))")
      eq(ms) == eq(mt) || error(
        "diagram $i does not commute")

      is_monic(st_map) && is_epic(st_map) || error(
        "leg map $i is not iso: $st_map")
      is_natural(s_leg)  || error("src leg $i not natural")
      is_natural(t_leg)  || error("tgt leg $i not natural")
      is_natural(st_map) || error("st_map  $i not natural")

    end
    return new{L}(s,t,m)
  end
end

dom(x::StructuredMultiCospanHom) = x.src
codom(x::StructuredMultiCospanHom) = x.tgt

"""
Find homomorphisms between structured cospans. These are constrained to be iso
on the legs of the cospans. Solving this w/ homomorphism finding  requires a
dynamic acset, and the current hack will be replaced once those are available.

A homomorphism backend that uses SAT/SMT would also make this viable to do
without hacking.
"""
function homomorphisms(pat::StructuredMulticospan{L},
                            tgt::StructuredMulticospan{L};
                            monic::Bool=false
                           )::Vector{StructuredMultiCospanHom{L}} where L
  # make modified ACSet that includes cospan info
  #----------------------------------------------
  V = L.parameters[1]
  p = Presentation(L.parameters[2]())
  Ls, ls = Symbol[], Symbol[]
  for i in 1:length(legs(pat))
    Leg, leg = Symbol("_Leg_$i"), Symbol("_leg_$i")
    push!(ls, leg)
    push!(Ls, Leg)
    add_generator!(p, Ob(FreeSchema, Leg))
    add_generator!(p, Hom(leg, p[Leg], p[V]))
  end

  t = AnonACSet(p, index=ls)
  # Copy old ACSet info from homomorphism source and target
  #--------------------------------------------------------
  tpat, ttgt = [deepcopy(t) for _ in 1:2]
  copy_parts!(tpat, apex(pat))
  copy_parts!(ttgt, apex(tgt))

  # Add leg data data to each ACset
  #--------------------------------
  for (Lname, lname, l) in zip(Ls, ls, legs(pat))
    add_parts!(tpat, Lname, nparts(dom(l), V); Dict([lname => collect(l[V])])...)
  end
  for (Lname, lname, l) in zip(Ls, ls, legs(tgt))
    add_parts!(ttgt, Lname, nparts(dom(l), V); Dict([lname => collect(l[V])])...)
  end

  # Compute homomorphisms in alternate schema
  #------------------------------------------
  matches = homomorphisms(tpat, ttgt, monic=monic, iso=Ls)

  # Process homomorphism finding results
  #-------------------------------------
  res = [StructuredMultiCospanHom(pat, tgt,
    [ACSetTransformation(apex(pat), apex(tgt);
                         Dict([k=>v for (k, v) in pairs(mtch.components)
                               if !(k in Ls)])...), # first map, on apexes
      [L(mtch[l]) for l in Ls]...]) # remaining maps, for each leg
    for mtch in matches]
  return res
end


function can_open_pushout_complement(f::StructuredMultiCospanHom{L},
                                     g::StructuredMultiCospanHom{L}
                                     )::Bool where L
  𝒞 = get_ACS(L)
  all([can_pushout_complement[𝒞](ComposablePair(a,b))
       for (a,b) in zip(f.maps, g.maps)])
end

"""A span of StructuredMulticospanHoms, interpreted as a DPO rewrite rule"""
struct openrule
  data::Span # Intended to be span of StructuredMulticospanHoms
end

get_ACS(L) = infer_acset_cat(typeof(L()).parameters[2]())

# Functions for the double category of structured multicospan rewrites
#---------------------------------------------------------------------
# Objects are finite sets (StructuredCospanOb{L})
# Horizontal arrows are structured multicospans
# Vertical arrows are spans of invertible finfunctions

function idH_(a::StructuredCospanOb{L}) where {L}
  x = L(FinSet(a.ob))
  i = id[get_ACS(L)](x)
  return StructuredCospan{L}(Cospan(x, i, i), a, a)
end

"""Vertical arrows are spans of invertible finfunctions"""
function idV_(a::StructuredCospanOb{L}) where {L}
  x = L(FinSet(a.ob))
  i = id[get_ACS(L)](x)
  return Span(i, i)
end

"""Cospan composition given by pushout"""
function composeH_(f::StructuredCospan{L}, g::StructuredCospan{L})::StructuredCospan{L} where {L}
  return compose(f,g)
end

"""Finset span composition given by pullback"""
function composeV_(f::Span, g::Span)::Span
  pbf, pbg = pullback(right(f), left(g))
  return Span(compose(pbf, left(f)), compose(pbg,right(g)))
end

function id2_(A::StructuredCospanOb{L})::openrule where {L}
  i = idH_(A)
  v = left(idV_(A))
  m = StructuredMultiCospanHom(i,i,[v,v,v])
  return openrule(Span(m,m))
end

"""
Pass dummy value in because a span of invertible FinFunctions does not retain
L type
"""
function id2H_(f::Span,_::StructuredCospanOb{L_})::openrule where {L_}
  Ll, Lr = L_.(f)
  sc     = idH_(StructuredCospanOb{L_}(dom(left(f))))
  up     = StructuredMultiCospanHom(sc, sc, [Ll, Ll, Ll])
  down   = StructuredMultiCospanHom(sc, sc, [Lr, Lr, Lr])
  return openrule(Span(up, down))
end

function id2V_(f::StructuredMulticospan{L})::openrule where {L}
  m = StructuredMultiCospanHom(f, f,
        vcat([id[get_ACS(L)](apex(f))], [id[get_ACS(L)](dom(x)) for x in legs(f)]))
  return openrule(Span(m,m))
end

"""    composeH_(r₁, r₂)
compose two rewrite rules horizontally (via pushouts) as shown below:
    L₁₋₍ₙ₋₁₎-> L <- Lₙ    X₁ -> X <- X₂₋ₘ     L₁₋₍ₙ₋₁₎ -> L +Lₙ X <- X₂₋ₘ
    ↑        λ ↑    ↑     ↑    ↑ χ    ↑          ↑           ↑        ↑
    I₁₋₍ₙ₋₁₎-> I <- Iₙ ∘h Y₁ -> Y <- Y₂₋ₘ  =  I₁₋₍ₙ₋₁₎ -> I +Iₙ Y <- Y₂₋ₘ
    ↓        ρ ↓    ↓     ↓    ↓ ζ    ↓          ↓           ↓        ↓
    R₁₋₍ₙ₋₁₎-> R <- Rₙ    Z₁ -> Z <- Z₂₋ₘ     R₁₋₍ₙ₋₁₎ -> R +Rₙ Z <- Z₂₋ₘ
 """
function composeH_(f::openrule, g::openrule)::openrule
  λ, ρ = f.data;
  χ, ζ = g.data;
  L = typeof(f.data).parameters[1].parameters[1]
  𝒞 = get_ACS(L)

  # we only care about equality up to i/o behavior (== considers indexing)
  non_indexed(x) = (dom(x), codom(x), collect.(values(components(x))))
  non_indexed(λ.maps[end]) == non_indexed(χ.maps[2]) || error(
    "cannot horizontally compose")
  non_indexed(ρ.maps[end]) == non_indexed(ζ.maps[2]) || error(
    "cannot horizontally compose")
  λapex, ρapex, χapex, ζapex = [m.maps[1] for m in [λ, ρ, χ, ζ]]
  IY = compose(dom(λ), dom(χ));
  LX = compose(codom(λ), codom(χ));
  RZ = compose(codom(ρ), codom(ζ));
  IY_pushout, LX_pushout, RZ_pushout = [
    pushout[𝒞](legs(left_cospan)[end],legs(right_cospan)[1])
     for (left_cospan,right_cospan) in
     [λ.src => χ.src, λ.tgt => χ.tgt,  ρ.tgt => ζ.tgt]];

  # Universal property, mapping out of a coproduct (into another coproduct)
  IY_LX = universal[𝒞](IY_pushout, Cospan(compose[𝒞](λapex, legs(LX_pushout)[1]),
                                       compose[𝒞](χapex, legs(LX_pushout)[2])));
  IY_RZ = universal[𝒞](IY_pushout, Cospan(compose[𝒞](ρapex, legs(RZ_pushout)[1]),
                                       compose[𝒞](ζapex, legs(RZ_pushout)[2])));
  IY_LX_maps = vcat([IY_LX], λ.maps[2:end-1], χ.maps[3:end])
  IY_RZ_maps = vcat([IY_RZ], ρ.maps[2:end-1], ζ.maps[3:end])
  IL = StructuredMultiCospanHom(IY, LX, IY_LX_maps);
  IR = StructuredMultiCospanHom(IY, RZ, IY_RZ_maps);
  return openrule(Span(IL, IR))
end


"""    composeV_(r₁, r₂)
compose two rewrite rules vertically with pullbacks, as shown below:
       L₁₋ₙ -> L
       ↑       ↑
       I₁₋ₙ -> I
       ↓       ↓         L₁₋ₙ        ->   L
       R₁₋ₙ -> R           ↑              ↑
           ∘v      = I₁₋ₙ ×ᵣ₁₋ₙ  Θ₁₋ₙ -> I ×ᵣ Θ
       Λ₁₋ₙ -> Λ           ↓              ↓
       ↑       ↑         Ω₁₋ₙ        ->   Ω
       Θ₁₋ₙ -> Θ
       ↓       ↓
       Ω₁₋ₙ -> Ω
"""
function composeV_(f_::openrule, g_::openrule)
  (lf, rf), (lg, rg) = (f, g) = f_.data, g_.data;
  L = typeof(left(f)).parameters[1];
  ACS = get_ACS(L)
  V= L.parameters[1]
  force(left(g).tgt) == force(right(f).tgt) || error("cannot compose $f and $g")
  pbs = [pullback[ACS](rf,lg) for (rf,lg) in zip(right(f).maps, left(g).maps)];
  upmaps = [compose[ACS](legs(pb)[1], lfm) for (pb, lfm) in zip(pbs, lf.maps)];
  dnmaps = [compose[ACS](legs(pb)[2], rgm) for (pb, rgm) in zip(pbs, rg.maps)];
  Imaps  = [compose[ACS](legs(pb)[1], im) for (pb, im) in zip(pbs[2:end], legs(lf.src))];
  Θmaps  = [compose[ACS](legs(pb)[2], θm) for (pb, θm) in zip(pbs[2:end], legs(rg.src))];
  xmaps  = [universal[ACS](pbs[1], Span(im, θm)) for (im, θm) in zip(Imaps, Θmaps)];
  newcenter = StructuredMulticospan{L}(
    apex(pbs[1]), Multicospan([xm[V] for xm in xmaps]));
  newl = StructuredMultiCospanHom(newcenter, lf.tgt, upmaps);
  newr = StructuredMultiCospanHom(newcenter, rg.tgt, dnmaps);
  return openrule(Span(newl, newr))
end


"""
Initial data: 4 structured cospans + 3 cospan morphisms: μ, λ, ρ
     g
G₁₋ₙ --> G
↑    l  ↑ μ
L₁₋ₙ --> L
↑    i  ↑ λ
I₁₋ₙ --> I
↓    r  ↓ ρ
R₁₋ₙ --> R

Computed data: 2 new structured cospans + 4 cospan morphisms: γ, η, ik, rh
        G₁₋ₙ      G
          ↑    k  ↑ γ   ik
 I₁₋ₙ -> K₁₋ₙ  --> K    <-- I
          ↓    h  ↓ η   rh
 R₁₋ₙ -> H₁₋ₙ  --> H    <-- R
In the context of the legs of a multicospan, the indices 1-n refer to the n
legs of the cospan. In the context of a map of multicospans, there are 1-(n+1)
maps, with the first one designating the map of the apexes. Hence it can make
sense to have the elements: zip(legs, maps[2:end]) = [(legᵢ, mapᵢ), ...]
"""
function open_pushout_complement(
    rule::openrule,
    μ::StructuredMultiCospanHom)::openrule

  # Unpack data
  L_ = typeof(left(rule.data)).parameters[1];
  ob = L_.parameters[1]
  λ, ρ = rule.data;
  I, R, G = dom(ρ), codom(ρ), codom(μ);
  𝒞 = get_ACS(L_)
  # Compute pushouts and pushout complements
  ik_γ = [pushout_complement[𝒞](λᵢ,μᵢ) for (λᵢ, μᵢ) in zip(λ.maps, μ.maps)];
  rh_η = [legs(pushout[𝒞](ρᵢ,ikᵢ)) for (ρᵢ, (ikᵢ, _)) in zip(ρ.maps, ik_γ)];
  rh, ik = rh_η[1][1], ik_γ[1][1]
  k = map(zip(legs(I), ik_γ[2:end])) do (iᵢ, (ikᵢ, _)) 
    foldl(compose[𝒞], [invert_iso(ikᵢ, [ob]), iᵢ, ik]) 
  end
  h = map(zip(legs(R), rh_η[2:end])) do (r₍, (rhᵢ, _))
    foldl(compose[𝒞], [invert_iso(rhᵢ, [ob]), r₍, rh]) 
  end

  # Reassemble resulting data into span of multicospans
  feetK = [FinSet(nparts(codom(ikᵢ), ob)) for (ikᵢ, _) in ik_γ[2:end]]
  feetH = [FinSet(nparts(codom(rhᵢ), ob)) for (rhᵢ, _) in rh_η[2:end]]
  K = StructuredMulticospan{L_}(Multicospan(k), feetK)
  H = StructuredMulticospan{L_}(Multicospan(h), feetH)
  maps_γ = ACSetTransformation[γᵢ for (_, γᵢ) in ik_γ]
  maps_η = ACSetTransformation[ηᵢ for (_, ηᵢ) in rh_η]
  γ = StructuredMultiCospanHom(K, G, maps_γ)
  η = StructuredMultiCospanHom(K, H, maps_η)
  return openrule(Span(γ, η))
end

"""
Extract the rewritten structured cospan from the induced rewrite rule
"""
function open_rewrite_match(
    rule::openrule, m::StructuredMultiCospanHom)::StructuredMulticospan
  right(open_pushout_complement(rule, m).data).tgt
end

"""
Apply a rewrite rule to a structured multicospan, where a matching cospan
homomorphism is found automatically. If multiple matches are found, a particular
one can be selected using `m_index`. Returns `nothing` if none are found.
"""
function open_rewrite(rule::openrule, G::StructuredMulticospan;
                      monic::Bool=false, m_index::Int=1)::StructuredMulticospan

  ms = filter(m->can_open_pushout_complement(left(rule.data), m),
              homomorphisms(left(rule.data).tgt, G, monic=monic))
  if 0 < m_index <= length(ms)
    open_rewrite_match(rule, ms[m_index])
  else
    nothing
  end
end

end # module