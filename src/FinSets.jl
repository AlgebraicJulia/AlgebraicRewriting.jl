module FinSets
export pushout_complement,can_pushout_complement,id_condition, is_injective, is_surjective
# once rewriting is removed from Catlab, we can import full namespace
using Catlab.Theories
using Catlab.CategoricalAlgebra: ComposablePair, FinSet, FinFunction

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
function pushout_complement(pair::ComposablePair{<:FinSet{Int}})
  l, m = pair
  I, L, G = dom(l), codom(l), codom(m)

  # Construct inclusion g: K ↪ G.
  l_image = Set(collect(l))
  m_image = Set([ m(x) for x in L if x ∉ l_image ])
  g = FinFunction([x for x in G if x ∉ m_image], G)
  K = dom(g)

  # Construct morphism k: I → K using partial inverse of g.
  g_inv = Dict{Int,Int}(zip(collect(g), K))
  k = FinFunction(map(I) do x
    y = m(l(x))
    get(g_inv, y) do; error("Identification failed for domain element $x") end
  end, I, K)

  return ComposablePair(k, g)
end

can_pushout_complement(pair::ComposablePair{<:FinSet{Int}}) =
  all(isempty, id_condition(pair))

""" Check identification condition for pushout complement of finite sets.

The identification condition says that the functions do not map (1) both a
deleted item and a preserved item in L to the same item in G or (2) two distinct
deleted items to the same item. It is trivially satisfied for injective functions.

Returns pair of iterators of

  (1) a nondeleted item that maps to a deleted item in G
  (2) a pair of distinct items in L that are deleted yet mapped to the same
      item in G.
"""
function id_condition(pair::ComposablePair{<:FinSet{Int}})
  l, m = pair
  l_image = Set(collect(l))
  l_imageᶜ = [ x for x in codom(l) if x ∉ l_image ]
  m_image = Set(map(m, l_imageᶜ))
  ((i for i in l_image if m(i) ∈ m_image),
   ((i, j) for i in eachindex(l_imageᶜ)
           for j in i+1:length(l_imageᶜ)
           if m(l_imageᶜ[i]) == m(l_imageᶜ[j])))
end

# These could be made to fail early if ever used in performance-critical areas
is_surjective(f::FinFunction) =
  length(codom(f)) == length(Set(values(collect(f))))
is_injective(f::FinFunction)  =
  length(dom(f)) == length(Set(values(collect(f))))

end