module FinSets
export pushout_complement,can_pushout_complement,id_condition

using Catlab.Theories
using Catlab.BasicSets, Catlab.CategoricalAlgebra
using ACSets.ColumnImplementations: AttrVar
using ACSets.DenseACSets: attrtype_type
using ..Theories
import ..Theories: pushout_complement

# Pushout complements
#--------------------

""" Compute a pushout complement of finite sets, if possible.

Given functions ``l: I → L`` and ``m: L → G`` to form a pushout square

    l
  L ← I
m ↓   ↓k
  G ← K
    g

define the set ``K := G / m(L / l(I))`` and take ``g: K ↪ G`` to be the
inclusion. Then the map ``k: I → K`` is determined by the map ``l⋅m: I → G``
from the requirement that the square commutes.

Pushout complements exist only if the identification condition is satisfied. An
error will be raised if the pushout complement cannot be constructed. To check
this in advance, use [`can_pushout_complement`](@ref).
"""
@instance ThPushoutComplement{FinSetInt, FinFunction
                             } [model::SkelFinSet] begin 
  function pushout_complement(pair::ComposablePair) 
    l, m = pair
    I, L, G = dom(l), codom(l), codom(m)
    # Construct inclusion g: K ↪ G.
    l_image = Set(collect(l))
    m_image = Set([ m(x) for x in L if x ∉ l_image ])
    g = FinFunction([x for x in G if x ∉ m_image], G)
    K = dom(g)

    # Construct morphism k: I → K using partial inverse of g.
    g_inv = Dict{Int,Int}(zip(collect(g), K))
    k = FinFunction(Vector{Int}(map(I) do x
      y = m(l(x))
      get(g_inv, y) do; error("Identification failed for domain element $x") end
    end), I, K)

    return ComposablePair(k, g)
  end

  pushout_complement_violations(p::ComposablePair) =
    vcat(collect.(id_condition(p...))...)
end

@instance ThPushoutComplement{FinSetInt, CopairedFinDomFunction{T, Int, Int}
                             } [model::SkelKleisli{T}] where T begin 
  function pushout_complement(pair::ComposablePair) 
    f, g = pair
    G = getvalue(g.L)
    x, y = compose[model](f, g), id[model](G)
    ComposablePair(x,y; cat=model)
  end

  pushout_complement_violations(p::ComposablePair) =
    vcat(collect.(id_condition(p...))...)

end


""" Compute a pushout complement of finite sets, if possible.

Given functions ``l: I → L`` and ``m: L → G`` to form a pushout square

    l
  L ← I
m ↓   ↓k
  G ← K
    g

define the set ``K := G ∖ m(L ∖ l(I))`` and take ``g: K ↪ G`` to be the
inclusion. Then the map ``k: I → K`` is determined by the map ``l⋅m: I → G``
from the requirement that the square commutes.

For example, if L = I = {1} and G = {1,2}, then  l({1}) = {1}, L ∖ l(I) = {}
and G∖ m({}) = {1,2}.

Pushout complements exist only if the identification condition is satisfied. An
error will be raised if the pushout complement cannot be constructed. To check
this in advance, use [`can_pushout_complement`](@ref).
"""
@instance ThPushoutComplement{FinSet, FinFunction
                             } [model::FinSetC] begin 
  function pushout_complement(pair::ComposablePair) 
    l, m = pair
    L, G = codom[model](l), codom[model](m)
    l_I = FinSet(ImgSet(l))
    L_min_l_I = FinSet(SetDiff(L,l_I))
    m_L_min_l_I = FinSet(ImgSet(postcompose[InclFunction(L_min_l_I, L)](m)))
    K = FinSet(SetDiff(G, m_L_min_l_I))
    g = FinFunction(InclFunction(K, G))
    k = FinFunction(RestrictFunction(compose[model](l,m), K))
    dom[model](g) == codom[model](k) == K || error(
      "Bad \n$K \n≠ \n$(dom[modle](g)) \n≠ \n$(codom[modle](k))")
    ComposablePair(k, g; cat=model)
  end

  pushout_complement_violations(p::ComposablePair) =
    vcat(collect.(id_condition(p...))...)

end

"""
Because l is monic, the map l:I+T ↣ L+T secretly is just a map l′:I↣L and T=T

We'll also assume that the map m: L+T->G+T is secretly just a map L->T (G=∅).
"""
@instance ThPushoutComplement{FinSet, CopairedFinDomFunction
                             } [model::KleisliC{T}] where T begin 
  function pushout_complement(pair::ComposablePair)
    l, m = pair
    k = id[model](dom[model](l))
    g = compose[model](l, m)
    typeof(k) ==  typeof(g) || error("Bad $(typeof(model))")
    ComposablePair(k, g; cat=model)
  end

  pushout_complement_violations(p::ComposablePair) =
    vcat(collect.(id_condition(p...))...)

end


""" Check identification condition for pushout complement of finite sets.

The identification condition says that the functions do not map (1) both a
deleted item and a preserved item in L to the same item in G or (2) two distinct
deleted items to the same item. It is trivially satisfied for injective functions.

Returns pair of iterators of

  (1) a nondeleted item that maps to a deleted item in G
  (2) a pair of distinct items in L that are deleted yet mapped to the same
      item in G.
"""
function id_condition(l::FinFunction, m::FinFunction)
  l_image = Set(collect(l))
  l_imageᶜ = [ x for x in codom(l) if x ∉ l_image ]
  m_image = Set(map(m, l_imageᶜ))
  ((i for i in l_image if m(i) ∈ m_image),
   ((i, j) for i in eachindex(l_imageᶜ)
           for j in i+1:length(l_imageᶜ)
           if m(l_imageᶜ[i]) == m(l_imageᶜ[j])))
end

""" Kleisli composition """
function id_condition(l::FinDomFunction, m::FinDomFunction)
  l_image = Set(collect(l))
  l_imageᶜ = [ x for x in dom(m) if Left(x) ∉ l_image ]
  m_image = Set(map(m, l_imageᶜ))
  err1 = filter(l_image) do i
    m(getvalue(i)) ∈ m_image
  end
  N = length(l_imageᶜ)
  err2 = []
  for i in 1:N, j in i+1:N 
    m((l_imageᶜ[i])) == m((l_imageᶜ[j])) && push!(l_imageᶜ[i], l_imageᶜ[j])
  end
  (err1, err2)
end

id_condition(l::CopairedFinDomFunction, m::CopairedFinDomFunction) = 
  id_condition(get(l), get(m))


end # module
