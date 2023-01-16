module Constraints 
export apply_constraint, Constraint, CGraph, Quantifier, AppCond, LiftCond
using Catlab, Catlab.CategoricalAlgebra, Catlab.Graphs
import ...CategoricalAlgebra.CSets: combinatorialize

# Constraints 
#############
"""
The general form of a constraint is a diagram in C-Set:

   X--->Y          X--->Y
   ↓ ↗  ↓            ↘  ↓           etc.
   A--> B               Z  

Where one of the arrows has been distinguished as the arrow we are "testing".
Some of the arrows are distinguished as "forall" or "exists". Certain squares 
/ triangles are marked as required to commute (or not commute).

∀f(X->Y) s.t. h⋅g=f, ∃u(A->Y) s.t. u⋅z=x & ∃v(A->Z) s.t. ϕ(v) & ψ(v)
"""


struct Quantifier 
  kind::Symbol                               # Forall, Exists, Exists!
  edges::Vector{Int}                         # quantified edges
  pos::Vector{Pair{Vector{Int},Vector{Int}}} # commuting paths
  neg::Vector{Pair{Vector{Int},Vector{Int}}} # non-commuting paths
  monic::Union{Bool,Vector{Symbol}}
  function Quantifier(kind, edges,;pos=[], neg=[], monic=false) 
    kind ∈ [:Forall, :Exists, :Exists!] || error("Unknown kkind $kind")
    for (p1,p2) in vcat(pos,neg) 
      err = "Every commutivity constraint must involve an quantified edge"
      !isempty(edges ∩ (p1 ∪ p2)) || error(err)
    end
    return new(kind, edges,pos,neg, monic)
  end
end 

const Assgn = Vector{Union{Nothing, <:ACSetTransformation}} # partial assignment

@present SchVLabeledGraph <: SchGraph begin
  (Label)::AttrType
  vlabel::Attr(V,Label)
end
@present SchVELabeledGraph <: SchGraph begin
  (VLabel,ELabel)::AttrType
  vlabel::Attr(V,VLabel)
  elabel::Attr(E,ELabel)
end

@acset_type VELabeledGraph(SchVELabeledGraph) <: AbstractGraph
@acset_type VLabeledGraph(SchVLabeledGraph) <: AbstractGraph

"""
Things to validate: 
- "nothing" vertex only if connected to nothing edge
"""
const CGraph = VELabeledGraph{Union{Nothing,StructACSet}, 
                                  Union{Nothing, ACSetTransformation}}
const CDag = VLabeledGraph{Quantifier}

"""
Get a list, each element containing a map for each edge in quantified edges, 
that satisfy the constraints
"""
function get_candidates(q::Quantifier, g::CGraph, curr::Assgn)
  # get all possible combinations of maps 
  all_homs = map(q.edges) do q_e
    d, cd = [get_ob(g,x,curr) for x in [g[q_e, :src], g[q_e, :tgt]]]
    homomorphisms(d, cd; monic=q.monic)
  end
  all_combos = map(Iterators.product(all_homs...)) do hom
    new_curr = deepcopy(curr)
    for (h_ind, h) in zip(q.edges, hom)
      new_curr[h_ind] = h
    end
    return new_curr
  end
  # filter by those which satisfy positive
  return filter(all_combos) do combo 
    return all([(true,q.pos),(false,q.neg)]) do (bool,pairs) 
      return all(pairs) do (p1, p2)
        root = get_ob(g, g[first(p1),:src], curr)
        return apply_equality(combo, root, p1, p2, bool)
      end
    end 
  end
end

struct Constraint
  g::CGraph 
  d::CDag 
  i::Int
  function Constraint(g,d,i)
    # check CGraph only has nothing vertices adjacent to edge i
    for v in vertices(g)
      if isnothing(g[v, :vlabel]) 
        e_in, e_out = incident(g, v, :src), incident(g, v, :tgt)
        (!all(isnothing, g[e_in, :elabel]) || !all(isnothing, g[e_out, :elabel]) 
         || i ∈ e_in || i ∈ e_out || error("Need to supply CSet for vertex $v"))
      end
    end
    topological_sort(d)
    all(filter(v->isempty(outneighbors(d,v)), vertices(d))) do leaf 
      d[leaf,:vlabel].kind ∈ [:Exists, :Exists!]
    end 
    return new(g,d,i)
  end 
end

function Constraint(g::CGraph, v::Vector{Quantifier}, i::Int)
  n = length(v)
  cdag = @acset CDag begin V=n; E=n-1; src=1:n-1; tgt=2:n; vlabel=v end 
  return Constraint(g, cdag, i)
end 


function eval_quantifier(c::Constraint, v::Int, curr::Assgn)
  println("EVALING QUANTIFIER $v")
  q = c.d[v, :vlabel] # the quantifier
  cands = get_candidates(q, c.g, curr)
  n = length(cands)
  println("$n candidates")
  out = outneighbors(c.d, v)
  if isempty(out)
    if q.kind == :Exists return n > 0
    elseif q.kind == :Exists! return n == 1
    else error("Bad terminal quantifier kind for leaf: $(q.kind)")
    end
  else 
    return any(outneighbors(c.d, v)) do next_v 
      n_success = length(filter(cand -> eval_quantifier(c, next_v, cand), cands))
      if     q.kind == :Exists  return n_success > 0
      elseif q.kind == :Exists! return n_success == 1
      elseif q.kind == :Forall  return n_success == n
      end
    end
  end
end

"""Get the C-Set associated with a vertex in a CGraph"""
function get_ob(c::CGraph, v_i::Int, curr::Assgn)
  if isnothing(c[v_i, :vlabel])
    for e_out in incident(c, v_i, :src)
      if !isnothing(curr[e_out]) return dom(curr[e_out]) end 
    end
    for e_in in incident(c, v_i, :tgt)
      if !isnothing(curr[e_in]) return codom(curr[e_in]) end 
    end
  else 
    return c[v_i, :vlabel] 
  end
end

function apply_constraint(c::Constraint, f::ACSetTransformation)
  ms = Assgn([e isa ACSetTransformation ? e : nothing for e in c.g[:elabel]])
  ms[c.i] = f 
  println("Starting with ms $ms")
  all(filter(v->isempty(inneighbors(c.d,v)), vertices(c.d))) do root_constr
    eval_quantifier(c, root_constr, deepcopy(ms))
  end
end


function apply_equality(choice::Vector{Union{Nothing, ACSetTransformation}}, 
                        root::StructACSet, p1::Vector{Int}, p2::Vector{Int},
                        commutes::Bool)
  lft, rght = map([p1,p2]) do pth 
    force(compose(id(root),[choice[e] for e in pth]...)) 
  end  
  return commutes == (lft == rght)
end

function combinatorialize(c::Constraint)
  g_ = deepcopy(c.g)
  for v in filter(v->!isnothing(g_[v, :vlabel]), vertices(g_))
    g_[v, :vlabel] = first(combinatorialize(g_[v,:vlabel]))
  end
  for e in filter(e->!isnothing(g_[e,:elabel]), edges(g_))
    g_[e, :elabel] = first(combinatorialize(g_[e,:elabel]))
  end
  Constraint(g_, c.d, c.i)
end 

# Special forms of constraints
##############################
"""
Constraint a constraint that asserts (or denies) the existence of a 
triangle commuting.

     f₁
(1) <- (2)
   ∃₂↘  ↓ λ₃
      (3)

"""
function AppCond(f::ACSetTransformation, pos::Bool)
  cg = @acset CGraph begin V=3; E=3; src=[2,1,2]; tgt=[1,3,3];
    vlabel=[codom(f), dom(f), nothing]; elabel=[f, nothing, nothing]
  end
  key = pos ? :pos : :neg
  return Constraint(cg, [Quantifier(:Exists,[2];Dict(key=>[[1,2]=>[3]])...)], 3)
end



"""
      ∀₂ 
 (1)  →  (3)
 ₁↓  ↗∃₃  ↓ λ₅
 (2)  →  (4)
      ⁴

Test a map (3)→(4), given maps (1)->(2)->(4). 
"""
function LiftCond(vertical::ACSetTransformation, bottom::ACSetTransformation)
  codom(vertical) == dom(bottom) || error("Composable pair required")
  A, B = dom.([vertical, bottom]); Y = codom(bottom)
  cg = @acset CGraph begin V=4; E=5; src=[1,1,2,2,3]; tgt=[2,3,3,4,4];
    vlabel=[A,B,nothing,Y]; elabel=[vertical, nothing, nothing, bottom, nothing]
  end
  F = Quantifier(:Forall, [2]; pos=[[2,5]=>[1,4]])
  E = Quantifier(:Exists, [3]; pos=[[1,3]=>[2], [3,5]=>[4]])
  return Constraint(cg, [F,E], 5)
end

end 