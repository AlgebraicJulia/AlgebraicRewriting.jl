module Poly 
export List, Maybe, Mealy, to_btree


"""
t = Σ_{I:t(1)} y^{t[I]}

I is the summand type 
Operad
"""
struct PMonad 
  I::Type
  η::Function # ∀A, A -> [I×A] 
  μ::Function # ∀A, [I×[I×A]]  -> [I×A] 
end

Maybe = PMonad(Nothing, 
               x  -> [(nothing,x)],
               xs -> isempty(xs) ? xs : only(xs))
function joinlist(xss; rem_dups=true)  
  i, res = 1, []
  for xs in xss 
    for (_,x) in xs 
      if !rem_dups
      push!(res, (i,x))
      i += 1
      end
    end
    return res
  end
end
List = PMonad(Int, x -> [(1,x)], xss -> joinlist)


"""A function that maintains a state"""
mutable struct Mealy
  f::Function # S × Σ A -> S × t ◁ Σ B
  t::PMonad  
  s::Any # current state
end

function (f::Mealy)(i::Int, v::Any)
  new_state, res = f.f(f.s, i, v)
  f.s = new_state 
  return res
end 

function to_btree(m::Mealy)
  K = Tuple{m.t.I,Tuple{Int,Any}} # tᵢ, Σᵢ a ∈ Aᵢ
  V = Function
  bt = BTree{K,V}((i,a)->deepcopy(m)(i,a))
  function f(ks::Vector{K′}) where K′
    error("HERE")
  end
  return InfBTree{K,V}(bt, f)
end 



"""
Lazily grown behavior tree. Vertices are 
functions ΣA -> t ◁ ΣB. Edges are pairs of (ΣA,tᵢ)
which determine how the tree branches based on the 
input and the monad summand index (i.e. index into 
the list of outputs).

    (f) (f) (f)
       ↖ ↑ ↗
        (f₀)

"""
struct BTree{K,V}
  branch::AbstractDict{K, BTree{K,V}}
  val::V
  BTree{K,V}(root::V) where {K,V} = new(Dict{K,BTree{K,V}}(),root)
end
Base.setindex!(b::BTree{K,V}, k::K, v::V) where {K,V} = b.branch[k] = v
function Base.setindex!(b::BTree{K,V}, ks::AbstractVector{K}) where {K,V}
  for k in ks[:end-1] b = b[k] end 
  b[last(ks)] = v
end
Base.getindex(b::BTree{K,V}, k::K) where {K,V} = b.branch[k]
function getindex!(b::BTree{K,V}, ks::AbstractVector{K}) where {K,V}
  for k in ks[:end-1] b = b[k] end 
  b[last(ks)]
end


"""A BTree that knows how to update itself"""
struct InfBTree{K,V}
  t::BTree{K,V}
  f::Function # Vector{K} -> V
end

(f::InfBTree{K,V})(k::K) where {K,V} = f([k])
  """Grow a tree and return the result"""
function (f::InfBTree{K,V})(ks::AbstractVector{K}) where {K,V}
  f.t[ks] = f.f(ks)
end



# Poly 
######

"""  ____
 ℕ -|    |- String 
 𝔹 -|S=ℕ |- Nothing
     -----
Machine receives a ℕ, it adds it to its internal state + returns nothing 
Machine recieves a 𝔹, it outputs symbol e.g. "True23" where the # is the state.
If the machine has state 10, it returns nothing.
"""
ex_fun(S::Int, i::Int, val::Any) = S == 10 ? (S, []) : ((
  i == 1 ? (S+val, [(nothing,(2,nothing))]) 
         : (S, [(nothing,(1,"$val$S"))])))
m = Mealy(ex_fun, Maybe, 0)
m(2,false) |> only
t = to_btree(m)
t.t.val(2,false)

t((2,false))


end # module
