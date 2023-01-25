module Constraints 
export apply_constraint, Constraint, CGraph, arity,
       Exists!, Forall, Exists, True, False, BoolOr, BoolAnd, BoolNot, Commutes,
       AppCond, LiftCond, Trivial
using Catlab, Catlab.CategoricalAlgebra, Catlab.Graphs
using StructEquality
import ...CategoricalAlgebra.CSets: Migrate

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
"nothing" means something tha twill be determined
AttrVars are explicit arguments provided when apply_constraint is called
"""
const CGraph = VELabeledGraph{Union{Nothing,StructACSet},Union{Nothing,ACSetTransformation}}

arity(g::CGraph) = let x = filter(v->v isa AttrVar, g[:elabel]); 
  isempty(x) ? 0 : maximum([v.val for v in x]) end

function (F::Migrate)(c::CGraph)
  c = deepcopy(c)
  c[:vlabel] = [x isa ACSet ? F(x) : x for x in c[:vlabel]]
  c[:elabel] = [x isa ACSetTransformation ? F(x) : x for x in c[:elabel]]
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
const True = BoolConst(true)
const False = BoolConst(false)

"""
e - which edge is filled in
"""
@struct_hash_equal struct Quantifier <: BoolExpr
  e::Int 
  kind::Symbol
  expr::BoolExpr 
  st::BoolExpr
  monic::Union{Bool,AbstractVector{Symbol}}
  Quantifier(e,k,x; st=True, monic=false) = 
    k ∈ [:Exists,:Forall,:Exists!] ? new(e,k,x,st,monic) : error("$k not supported")
end

Exists!(e,x;st=True,monic=false) = Quantifier(e,:Exists,x;st=st,monic=monic)
Forall(e,x;st=True,monic=false) = Quantifier(e,:Forall,x;st=st,monic=monic)
Exists(e,x;st=True,monic=false) = Quantifier(e,:Exists,x;st=st,monic=monic)

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
eval_boolexpr(c::BoolAnd, g::CGraph, m::Assgn) = 
  all(eval_boolexpr(x,g,m) for x in c.exprs)
eval_boolexpr(c::BoolOr, g::CGraph, m::Assgn) = 
  any(eval_boolexpr(x,g,m) for x in c.exprs)

function eval_boolexpr(c::Commutes, ::CGraph, ms::Assgn)
  maps = [force(length(p)==1 ? ms[p[1]] : compose(ms[p]...)) for p in c.pths]
  return c.commutes == (all(m->m==maps[1],maps))
end 

function eval_boolexpr(q::Quantifier, g::CGraph, curr::Assgn)
  d, cd = [get_ob(g,x,curr) for x in [g[q.e, :src], g[q.e, :tgt]]]
  cands = []
  for h in homomorphisms(d, cd; monic=q.monic)
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
  Constraint(g,d)= new(g,d)
end
arity(g::Constraint) = arity(g.g)

(F::Migrate)(c::Constraint) = Constraint(F(c.g),c.d)
const Trivial = Constraint(CGraph(), True)

"""Get the C-Set associated with a vertex in a CGraph"""
function get_ob(c::CGraph, v_i::Int, curr::Assgn)
  if c[v_i, :vlabel] isa ACSet return c[v_i, :vlabel]  end
  for e_out in incident(c, v_i, :src)
    if !isnothing(curr[e_out]) return dom(curr[e_out]) end 
  end
  for e_in in incident(c, v_i, :tgt)
    if !isnothing(curr[e_in]) return codom(curr[e_in]) end 
  end
  error("Failed to get ob")
end

function apply_constraint(c::Constraint, fs...)
  # populate assignment of ACSetTransformations 
  ms = Assgn(map(enumerate(c.g[:elabel])) do (i, e) 
    if e isa ACSetTransformation 
      return e 
    elseif e isa AttrVar 
      return fs[e.val]
    end
  end)
  return eval_boolexpr(c.d, c.g, ms)  # Evaluate expression
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
function AppCond(f::ACSetTransformation, pos::Bool=true; monic=false)
  cg = @acset CGraph begin V=3; E=3; Elabel=1; src=[2,1,2]; tgt=[1,3,3];
    vlabel=[codom(f), dom(f), nothing]; elabel=[f, nothing, AttrVar(1)]
  end
  expr = Exists(2, Commutes([1,2],[3]); monic=monic)
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
function LiftCond(vertical::ACSetTransformation, bottom::ACSetTransformation; 
                  monic_all=false, monic_exists=false)
  codom(vertical) == dom(bottom) || error("Composable pair required")
  A, B = dom.([vertical, bottom]); Y = codom(bottom)
  cg = @acset CGraph begin V=4; E=5; Elabel=1; src=[1,1,2,2,3]; tgt=[2,3,3,4,4]
    vlabel=[A,B,nothing,Y]; elabel=[vertical, nothing, nothing, bottom, AttrVar(1)]
  end
  expr = Forall(2, Exists(3, BoolAnd(Commutes([1,3],[2]), Commutes([3,5],[4])); 
                          monic=monic_exists);
                st=Commutes([2,5],[1,4]), monic=monic_all)
  return Constraint(cg, expr)
end

end 