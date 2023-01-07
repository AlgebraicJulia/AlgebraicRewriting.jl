module RewriteDataStructures 
export Rule, PAC, NAC

using StructEquality

using Catlab.CategoricalAlgebra

import Catlab.Theories: dom, codom
import Catlab.CategoricalAlgebra: is_natural,components
using Catlab.CategoricalAlgebra.DataMigrations: MigrationFunctor
using Catlab.CategoricalAlgebra.CSets: type_components


# Application conditions
########################
"""
Application conditions, either positive or negative.

This can be attached to a rule as a morphism f: L->AC. When a match morphism is 
found, we are concerned with triangles:
 AC <-- L <-- I --> R
    ↘  ↓
      G
  
If the condition is positive, we demand that the triangle commutes for the match 
to be considered valid. If it is negative, we forbid such a triangle.

An important subtlety is that monicity is only checked during AC evaluation
for the elements that are *not* assigned in virtue of the match morphism. Here
is an example:

L is a single vertex but we want to match vertices with at most one inneighbor.
AC has (a cospan shape), since the two inneighbors might be
different (therefore, the match constraint is not monic).
"""
struct AppCond
  f::ACSetTransformation
  positive::Bool
  monic::Union{Bool, Vector{Symbol}}
  init_check::Bool
  AppCond(f::ACSetTransformation, p=false, m=false, init_check=true) = 
    new(f, p, m, init_check)
end

AppCond(nac::AppCond) = nac
pos(nac::AppCond) = nac.positive ? "Positive" : "Negative"
NAC(f::ACSetTransformation, m=false, init_check=true) = AppCond(f,false,m,init_check)
PAC(f::ACSetTransformation, m=false, init_check=true) = AppCond(f,true,m,init_check)
codom(n::AppCond) = codom(n.f)
dom(n::AppCond) = dom(n.f)
is_natural(n::AppCond) = is_natural(n.f)
components(n::AppCond) = components(n.f)
(F::DeltaMigration)(n::AppCond) = AppCond(F(n.f), n.positive, n.monic, n.init_check)

# RULES 
#######

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
struct Rule{T}
  L::Any
  R::Any
  conditions::Vector{AppCond}
  monic::Union{Bool, Vector{Symbol}}
  exprs::Dict{Symbol, Vector{Expr}}
  function Rule{T}(L, R; ac=nothing, monic=false, expr=nothing) where {T}
    dom(L) == dom(R) || error("L<->R not a span")
    ACs = Vector{AppCond}(isnothing(ac) ? [] : (ac isa AbstractVector ? ac : [NAC(ac)]))
    exprs = isnothing(expr) ? Dict() : expr
    all(N-> dom(N) == codom(L), ACs) || error("AppCond does not compose with L $(codom(L))")
    map(enumerate([L,R,ACs...])) do (i, f)
      if !is_natural(f)
        show(stdout, "text/plain",dom(f))
        show(stdout, "text/plain",codom(f))
        println("cs(f) $(components(f)) \ntype_cs $(type_components(f))")
        error("unnatural map #$i: $f")
      end
    end
    for (o, xs) in collect(exprs)
      n = nparts(codom(R),o) - nparts(dom(R), o)
      n == length(xs) || error("$n exprs needed for part $o")
    end 
    new{T}(L, R, ACs, monic, exprs)
  end
end

Rule(l,r;kw...) = Rule{:DPO}(l,r; kw...)

ruletype(::Rule{T}) where T = T


(F::DeltaMigration)(r::Rule{T}) where {T} =
  Rule{T}(F(r.L), F(r.R), F.(r.conditions); monic=r.monic)


end # module 
