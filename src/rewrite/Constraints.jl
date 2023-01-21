module Constraints 
export apply_constraint, Constraint, CGraph, 
       Quantifier,BoolOr,BoolAnd,BoolNot,Commutes,
       AppCond, LiftCond
using Catlab, Catlab.CategoricalAlgebra, Catlab.Graphs
using StructEquality
import ...CategoricalAlgebra.CSets: combinatorialize, Migrate

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
# const CDag = VLabeledGraph{Quantifier}
function (F::Migrate)(c::CGraph)
  c = deepcopy(c)
  c[:vlabel] = [isnothing(x) ? x : F(x) for x in c[:vlabel]]
  c[:elabel] = [isnothing(x) ? x : F(x) for x in c[:elabel]]
  return c
end


abstract type BoolExpr end 
@struct_hash_equal struct Commutes <: BoolExpr 
  pths::Vector{Vector{Int}}
  commutes::Bool 
  function Commutes(p...; commutes=true)
    !(any(isempty, p) || isempty(p)) || error("Paths cannot be empty")
    return new(collect(p),commutes)
  end
end

@struct_hash_equal struct BoolConst <: BoolExpr 
  val::Bool
end 

@struct_hash_equal struct Quantifier <: BoolExpr
  e::Int 
  kind::Symbol
  expr::BoolExpr 
  st::BoolExpr
  Quantifier(e,k,x; st=BoolConst(true)) = k ∈ [:Exists,:Forall,:Exists!] ? new(
    e,k,x,st) : error("$k not supported")
end 
@struct_hash_equal struct BoolOr <: BoolExpr 
  exprs::Vector{BoolExpr}
  BoolOr(x...) = new(collect(x))
end 
@struct_hash_equal struct BoolAnd <: BoolExpr 
  exprs::Vector{BoolExpr}
  BoolAnd(x...) = new(collect(x))
end 
@struct_hash_equal struct BoolNot <: BoolExpr 
  expr::BoolExpr
end 

bound(::BoolConst) = Set{Int}([])
bound(b::BoolOr) = union(bound.(b.exprs)...)
bound(b::BoolAnd) = union(bound.(b.exprs)...)
bound(b::BoolNot) = bound(b.expr)
bound(b::Quantifier) = Set([b.e]) ∪ bound(b.expr)
bound(::Commutes) = Set{Int}([])

eval_boolexpr(c::BoolConst, ::CGraph, ::Assgn) = c.val
eval_boolexpr(c::BoolNot, g::CGraph, m::Assgn) = !eval_boolexpr(c.expr,g,m)
eval_boolexpr(c::BoolAnd, g::CGraph, m::Assgn) = all(eval_boolexpr(x,g,m) for x in c.exprs)
eval_boolexpr(c::BoolOr, g::CGraph, m::Assgn) = any(eval_boolexpr(x,g,m) for x in c.exprs)
function eval_boolexpr(c::Commutes, ::CGraph, ms::Assgn)
  # for p in c.pths println("p $p ms[p] $(ms[p])") end
  maps = [force(length(p)==1 ? ms[p[1]] : compose(ms[p]...)) for p in c.pths]
  return c.commutes == (all(m->m==maps[1],maps))
end 
function eval_boolexpr(q::Quantifier, g::CGraph, curr::Assgn)
  d, cd = [get_ob(g,x,curr) for x in [g[q.e, :src], g[q.e, :tgt]]]
  cands = []
  for h in homomorphisms(d, cd)
    x = deepcopy(curr)
    x[q.e] = h 
    if eval_boolexpr(q.st, g, x)
      push!(cands, x)
    end
  end 
  n = length(cands)
  suc = [eval_boolexpr(q.expr, g, cand) for cand in cands]
  n_success = sum([0, suc...])
  if     q.kind == :Exists  return n_success > 0
  elseif q.kind == :Exists! return n_success == 1
  elseif q.kind == :Forall  return n_success == n
  end
end 

@struct_hash_equal struct Constraint
  g::CGraph 
  d::BoolExpr 
  i::Int
  function Constraint(g,d,i=0)
    i = i == 0 ? only(setdiff(findall(isnothing, g[:elabel]), bound(d))) : i
    # check CGraph only has nothing vertices adjacent to edge i
    for v in vertices(g)
      if isnothing(g[v, :vlabel]) 
        e_in, e_out = incident(g, v, :src), incident(g, v, :tgt)
        (!all(isnothing, g[e_in, :elabel]) || !all(isnothing, g[e_out, :elabel]) 
         || i ∈ e_in || i ∈ e_out || error("Need to supply CSet for vertex $v"))
      end
    end
    return new(g,d,i)
  end 
end

function Constraint(g::CGraph, v::Vector{Quantifier}, i::Int)
  n = length(v)
  cdag = @acset CDag begin V=n; E=n-1; src=1:n-1; tgt=2:n; vlabel=v end 
  return Constraint(g, cdag, i)
end 

(F::Migrate)(c::Constraint) = Constraint(F(c.g),c.d, c.i)

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
  eval_boolexpr(c.d, c.g, ms)
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
function AppCond(f::ACSetTransformation, pos::Bool=true)
  cg = @acset CGraph begin V=3; E=3; src=[2,1,2]; tgt=[1,3,3];
    vlabel=[codom(f), dom(f), nothing]; elabel=[f, nothing, nothing]
  end
  expr = Quantifier(2, :Exists, Commutes([1,2],[3]))
  return Constraint(cg, pos ? expr : BoolNot(expr))
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
  expr = Quantifier(2, :Forall,
  Quantifier(3, :Exists, BoolAnd(Commutes([1,3],[2]), Commutes([3,5],[4])));
    st=Commutes([2,5],[1,4]))
  return Constraint(cg, expr)
end

end 