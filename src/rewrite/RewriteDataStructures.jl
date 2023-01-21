module RewriteDataStructures 
export AbsRule, Rule, PAC, NAC, AppCond, LiftCond, PBPORule, AttrPBPORule, 
       ruletype

using StructEquality

using Catlab.CategoricalAlgebra, Catlab.Graphs

import Catlab.Theories: dom, codom
import Catlab.CategoricalAlgebra: is_natural,components, left, right
using Catlab.CategoricalAlgebra.DataMigrations: MigrationFunctor
using Catlab.CategoricalAlgebra.CSets: type_components
using ...CategoricalAlgebra.CSets: check_pb, extend_morphism, combinatorialize, 
                                   extend_morphisms, Migrate
using ..Constraints

# RULES 
#######
abstract type AbsRule end 

"""
Rewrite rules which are encoded as spans. 
The L structure encodes a pattern to be matched. 
The R morphism encodes a replacement pattern to be substituted in.
They are related to each other by an interface I with maps: L ⟵ I ⟶ R 

A semantics (DPO, SPO, or SqPO) must be chosen.

Control the match-finding process by specifying whether the match is
intended to be monic or not, as well as an optional application
condition(s) 

Monic constraints can be independently given
to the match morphism and to the morphisms searched for when checking NAC.
"""
struct Rule{T} <: AbsRule
  L::Any
  R::Any
  conditions::Vector{Constraint} # constraints on match morphism
  monic::Union{Bool, Vector{Symbol}}
  exprs::Dict{Symbol, Vector{<:Function}}
  function Rule{T}(L, R; ac=nothing, monic=false, expr=nothing) where {T}
    dom(L) == dom(R) || error("L<->R not a span")
    ACs = isnothing(ac) ? [] : ac
    exprs = isnothing(expr) ? Dict() : Dict(pairs(expr))
    map(enumerate([L,R,])) do (i, f)
      if !is_natural(f)
        error("unnatural map #$i: $f")
      end
    end
    for (o, xs) in collect(exprs)
      nparts(codom(R),o) == length(xs) || error("$(nparts(codom(R),o)) exprs needed for part $o")
    end 
    new{T}(L, R, ACs, monic, exprs)
  end
end

Rule(l,r;kw...) = Rule{:DPO}(l,r; kw...)
ruletype(::Rule{T}) where T = T
left(r::Rule{T}) where T = r.L
right(r::Rule{T}) where T = r.R

(F::Migrate)(r::Rule{T}) where {T} =
  Rule{T}(F(r.L), F(r.R); ac=F.(r.conditions), expr=r.exprs, monic=r.monic)

# PBPO 
######

"""
      l    r 
   L  ⟵ K ⟶ R 
tl ↓     ↓ tk     <== these must be monic
   L' ⟵ K'

It is assumed we never want the typing/adherence match to be monic, but we 
can optionally restrict the match L → G to be monic.

We can attach positive/negative application conditions to both the match 
morphism as well as the adherence morphism. These are qualitatively different.

Application conditions to the match morphism know nothing of the typing (this is 
because we compute the match morphism first). These are morphisms L -> C 

Restrictions to the typing morphism are in the form of lifting conditions in 
the category G/L′. So we have arbitrary morphisms A/L′->B/L′ and consider 
triangles:

    A/L′ ↪ B/L′
   ∀ ↓   ↙   <--- this arrow either must exist (pos) or must not exist (neg)
    G/L′  
"""
struct PBPORule <: AbsRule
  l
  r
  tl
  tk 
  l′
  monic::Union{Bool, Vector{Symbol}}
  acs::Vector{Constraint}
  lcs::Vector{Constraint}
  function PBPORule(l,r,tl,tk,l′; monic=true, acs=[], lcs=[])
    # check things match up
    all(is_natural, [l,r,tl,tk,l′]) || error("Unnatural")
    dom(l) == dom(r) == dom(tk) || error("bad K")
    codom(l) == dom(tl) || error("bad L")
    codom(tk) == dom(l′) || error("bad K'")
    codom(l′) == codom(tl) || error("bad L'")
    check_pb(tl,l′,l,tk) || error("(l,tk) not the pullback of (tl,l′)")
    is_monic(tl) || error("tl map must be monic $tl")
    is_monic(tk) || error("tk map must be monic $tk")
    # check adherence conditions?
    return new(l,r,tl,tk,l′, monic, acs, lcs)
  end
end

ruletype(::PBPORule) = :PBPO
left(r::PBPORule) = r.l 
right(r::PBPORule) = r.r


"""
Take a PBPO rule and put into normal form, i.e. 
where the lower square forms a pullback

See Prop 2.4 of "The PBPO graph transformation approach"
"""
function canon(l,r,tl,tk,l′)::PBPORule
  new_l , new_tk = pb = pullback(tl, l′)
  ns = filter(n->force(n⋅new_tk)==force(tk), 
              homomorphisms(dom(l), apex(pb)))
  n = only(ns) # is there a better way to get this via pullback?
  new_r, _ = pushout(n, r)
  PBPORule(force.([new_l, new_r, tl, new_tk,l′])...)
end

"""
TODO: ACS/LCS cannot have non-variable valued attributes yet. Need to add some 
additional constraint to the conditions after they are combinatorialized to 
reflect ACSetTransformation constraint.
"""
struct AttrPBPORule <: AbsRule
  l
  r
  tl
  tk 
  l′
  monic::Union{Bool, Vector{Symbol}}
  combo_rule::PBPORule 
  dicts::Dict
  exprs::Vector{Expr}
  k_exprs::Dict
  acs::Vector{Constraint}  # constrains match
  lcs::Vector{Constraint} # constrains αdherence
  function AttrPBPORule(l,r,tl,tk,l′; monic=true, exprs=nothing, k_exprs=nothing,
                        acs=AppCond[], lcs=LiftCond[])
    # check things match up
    all(is_natural, [l,r,tl,tk,l′]) || error("Unnatural")
    dom(l) == dom(r) == dom(tk) || error("bad K")
    codom(l) == dom(tl) || error("bad L")
    codom(tk) == dom(l′) || error("bad K'")
    codom(l′) == codom(tl) || error("bad L'")
    is_monic(tl) || error("tl map must be monic $tl")
    is_monic(tk) || error("tk map must be monic $tk")

    # Combinatorialize 
    l_combo, K_combo, L_combo = combinatorialize(l)
    r_combo, _, R_combo = combinatorialize(r)
    tl_combo, _, L′_combo = combinatorialize(tl)
    tk_combo, _, K′_combo = combinatorialize(tk)
    l′_combo, _, _ = combinatorialize(l′)
    dicts = Dict(:L=>L_combo, :K=>K_combo, :R=>R_combo, :L′=>L′_combo, :K′=>K′_combo)
    acs_ = [combinatorialize(ac) for ac in acs]
    lcs_ = [combinatorialize(lc) for lc in lcs]

    rule = PBPORule(l_combo, r_combo, tl_combo, tk_combo, l′_combo; 
                    monic=monic, acs=acs_, lcs=lcs_) 

    exprs = isnothing(exprs) ? Expr[] : exprs
    k_exprs = isnothing(k_exprs) ? Dict() : k_exprs

    return new(l,r,tl,tk,l′, monic, rule, dicts, exprs, k_exprs, acs_, lcs_)
  end
end
ruletype(::AttrPBPORule) = :AttrPBPO


end # module 
