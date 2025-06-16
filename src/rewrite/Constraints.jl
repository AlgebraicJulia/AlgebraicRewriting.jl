module Constraints 
export apply_constraint, Constraint, CGraph, arity,
       ∀, ∃, ∃!, True, False, Commutes,
       AppCond, LiftCond, Trivial, PAC, NAC
using Catlab
import Catlab.Theories: ⊗, ⊕
import Catlab.CategoricalAlgebra: ¬
import Catlab.Graphics: to_graphviz
using StructEquality
import ...CategoricalAlgebra.CSets: Migrate
import ACSets: sparsify

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

# Diagrams with some edges flagged as literals, variables, or quantified over
#############################################################################

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
"nothing" means something that will be determined via a quantifier
Ints are explicit arguments provided when apply_constraint is called
"""
const CGraph = VELabeledGraph{Union{Nothing, ACSet},
                              Union{Nothing, Int, ACSetTransformation}}
𝒞CGrph = ACSetCategory(VarACSetCat(CGraph()))

"""Number of variables in a constraint graph"""
arity(g::CGraph) = maximum(filter(v->v isa Int, g[:elabel]); init=0) 

"""Apply migration to all literals in the constraint"""
function (F::Migrate)(c::CGraph)
  c = deepcopy(c)
  c[:vlabel] = [x isa ACSet ? F(x) : x for x in c[:vlabel]]
  c[:elabel] = [x isa ACSetTransformation ? F(x) : x for x in c[:elabel]]
  return c
end
function sparsify(c::CGraph)
  c = deepcopy(c)
  c[:vlabel] = [x isa ACSet ? sparsify(x) : x for x in c[:vlabel]]
  c[:elabel] = [x isa ACSetTransformation ? sparsify(x) : x for x in c[:elabel]]
  return c
end

"""
Take two CGraphs and merge them along their overlapping vertices and edges
Returns an ACSetColimit
"""
function merge_graphs(g1,g2)
  # Vertices with literal acsets on them that match
  overlap_g = CGraph()
  p1, p2 = [Dict(:V=>Int[], :E=>Int[]) for _ in 1:2]
  # Merge vertices
  for (v1,X) in filter(x->x[2] isa ACSet, collect(enumerate(g1[:vlabel])))
    v2 = findfirst(==(X), g2[:vlabel])
    if !isnothing(v2)
      add_vertex!(overlap_g; vlabel=X)
      push!(p1[:V], v1); push!(p2[:V], v2); 
    end
  end 
  # Merge literal edges
  for (e1,X) in filter(x->x[2] isa ACSetTransformation, collect(enumerate(g1[:elabel])))
    src1, tgt1 = g1[e1,:src], g1[e1,:tgt]
    e2 = findfirst(==(X), g2[:elabel])
    if !isnothing(e2)
      add_edge!(overlap_g, p1[:V][src1], p1[:V][tgt1]; elabel=X)
      push!(p1[:E], e1); push!(p2[:E], e2); 
    end
  end 
  # Merge variable edges 
  i1, i2 = [collect(filter(x->x isa Int, g[:elabel])) for g in [g1,g2]]
  for v in i1 ∩ i2
    e1,e2 = [findfirst(==(v), g[:elabel]) for g in [g1,g2]]
    src1, tgt1 = g1[e1,:src], g1[e1,:tgt]
    src2, tgt2 = g2[e1,:src], g2[e1,:tgt]
    if src1 ∉ p1[:V]
      s = add_vertex!(overlap_g; vlabel=g1[src1, :vlabel])
      push!(p1[:V], src1); push!(p2[:V], src2); 
    else
      s = findfirst(==(src1), p1[:V])
    end
    if tgt1 ∉ p1[:V]
      t = add_vertex!(overlap_g; vlabel=g1[tgt1, :vlabel])
      push!(p1[:V], tgt1); push!(p2[:V], tgt2);
    else
      t = findfirst(==(tgt1), p1[:V])
    end
    add_edge!(overlap_g, s, t; elabel=v)
    push!(p1[:E], e1); push!(p2[:E], e2); 
  end 
  ps = [ACSetTransformation(overlap_g, g; p..., cat=𝒞CGrph) for (g,p) in [(g1,p1),(g2,p2)]]
  for (i,p) in enumerate(ps) 
    errs = naturality_failures(p; cat=𝒞CGrph)
    all(isempty,values(errs)) || error( "UNNATURAL $i: $errs\n$(components(p))")
  end
  return colimit[𝒞CGrph](Span(ps...))
end

# Interpreter for boolean algebra
#################################
const Assgn = Vector{Union{Nothing, <:ACSetTransformation}} # partial assignment
paren(x) = "($x)" 

"""Something that, in a context, can be evaluated to a bool"""
abstract type BoolExpr end 
check_expr(::CGraph, ::BoolExpr) = error("Method undefined")
bound(::BoolExpr) = error("Method undefined")
eval_boolexpr(::BoolExpr, ::CGraph, ::Assgn; cat) = error("Method undefined")
map_edges(_, _::BoolExpr) = error("Method undefined")
subexprs(::BoolExpr) = error("Method undefined")

"""
A commutative diagram with multiple parallel paths, asserted to either 
commute or to not commute
"""
@struct_hash_equal struct Commutes <: BoolExpr 
  pths::Vector{Vector{Int}}
  commutes::Bool 
  function Commutes(p...; commutes=true)
    !(any(isempty, p) || isempty(p)) || error("Paths cannot be empty")
    return new(collect(p),commutes)
  end
end

subexprs(::Commutes) = BoolExpr[]
Base.show(io::IO, c::Commutes) =
  join(io, [join(p, "⋅") for p in c.pths], c.commutes ? " = " : " ≠ ")

"""Constant, independent of context"""
@struct_hash_equal struct BoolConst <: BoolExpr 
  val::Bool
end 
Base.show(io::IO, c::BoolConst) = print(io, c.val ? "⊤" : "⊥")
subexprs(::BoolConst) = BoolExpr[]

const True = BoolConst(true)
const False = BoolConst(false)

"""
Quantified edge

e - which edge is filled in
kind - Exists, Forall, or Exists! 
st - "such that", restrict the domain of quantification via a condition
monic - restrict domain of quanitification to only monic matches
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

quantifier_symbol(c::Quantifier) = if     c.kind == :Exists  "∃"
                                   elseif c.kind == :Forall  "∀"
                                   elseif c.kind == :Exists! "∃!"
                                   end

function Base.show(io::IO, c::Quantifier)
  q = quantifier_symbol(c)
  m = if c.monic isa AbstractVector
    "monic{$(join(c.monic, ","))}, "
  elseif c.monic 
    "monic, "
  else
    ""
  end
  st = c.st == True ? "" : paren(c.st)
  mst = isempty(m*st) ? "" : " $(paren(m*st))"
  x = c.expr == True && c.kind ∈ [:Exists, :Exists!] ? "" : ": $(paren(c.expr))"
  print(io, join([q,c.e,mst,x]))
end
subexprs(q::Quantifier) = [q.expr, q.st]

Exists!(e,x; st=True, monic=false) = Quantifier(e,:Exists,x; st, monic)
Forall(e, x; st=True, monic=false) = Quantifier(e,:Forall,x; st, monic)
Exists(e, x; st=True, monic=false) = Quantifier(e,:Exists,x; st, monic)
∀(args...; kwargs...) = Forall(args...; kwargs...)
∃(args...; kwargs...) = Exists(args...; kwargs...)
∃!(args...; kwargs...) = Exists!(args...; kwargs...)

"""Disjunction of multiple expressions"""
@struct_hash_equal struct BoolOr <: BoolExpr 
  exprs::Vector{BoolExpr}
  BoolOr(x...) = new(collect(filter(!=(False),x)))
end

Base.show(io::IO, b::BoolOr) = 
  if isempty(b.exprs) 
    print(io, False)
  else 
    join(io, paren.(b.exprs), " ∨ ")
  end

subexprs(b::BoolOr) = b.exprs

⊕(xs::BoolExpr...) = BoolOr(xs...)

"""Conjunction of multiple expressions"""
@struct_hash_equal struct BoolAnd <: BoolExpr 
  exprs::Vector{BoolExpr}
  BoolAnd(x...) = new(collect(filter(!=(True),x)))
end

Base.show(io::IO, b::BoolAnd) = 
  if isempty(b.exprs) 
    show(io, True)
  else 
    join(io, paren.(b.exprs), " ∧ ")
  end
subexprs(b::BoolAnd) = b.exprs

⊗(xs::BoolExpr...) = BoolAnd(xs...) 

"""Negation of an expression"""
@struct_hash_equal struct BoolNot <: BoolExpr 
  expr::BoolExpr
end 
subexprs(b::BoolNot) = [b.expr]
Base.show(io::IO, b::BoolNot) = print(io, "¬$(b.expr isa Quantifier ? b.expr : paren(b.expr))") 

¬(x::BoolExpr) = BoolNot(x)

"""Validate a commutative diagram constraint makes sense"""
function check_expr(g::CGraph, c::Commutes)
  viol = String[]  
  # check paths are parallel 
  srcs = unique([g[first(p),:src] for p in c.pths])
  length(srcs) == 1 || push!(viol,"Paths don't share common src $srcs ")
  tgts = unique([g[last(p),:tgt] for p in c.pths])
  length(tgts) == 1 || push!(viol, "Paths don't share common tgt $tgts ")
  for (i,p) in enumerate(c.pths)  # check each path matches head to tail 
    for (e1, e2) in zip(p, p[2:end])
      g[e1,:tgt] == g[e2, :src] || push!(viol, "Path $i doesn't compose $p")
    end
  end
  return viol
end
check_expr(g::CGraph, c::Quantifier) = vcat(
  isnothing(g[c.e, :elabel]) ? [] : ["quantified var $(c.e) already assigned"], 
  check_expr(g, c.expr), check_expr(g, c.st))

check_expr(::CGraph, ::BoolConst) = String[]
check_expr(g::CGraph, a::BoolAnd) = vcat([check_expr(g,e) for e in a.exprs]...)
check_expr(g::CGraph, a::BoolOr) = vcat([check_expr(g,e) for e in a.exprs]...)
check_expr(g::CGraph, a::BoolNot) = check_expr(g,a.expr)


bound(::BoolConst) = Set{Int}([])
bound(b::BoolOr) = union(bound.(b.exprs)...)
bound(b::BoolAnd) = union(bound.(b.exprs)...)
bound(b::BoolNot) = bound(b.expr)
bound(b::Quantifier) = Set([b.e]) ∪ bound(b.expr)
bound(::Commutes) = Set{Int}([])

eval_boolexpr(c::BoolConst, ::CGraph, ::Assgn; cat) = c.val
eval_boolexpr(c::BoolNot, g::CGraph, m::Assgn; cat) = 
  !eval_boolexpr(c.expr, g, m; cat)
eval_boolexpr(c::BoolAnd, g::CGraph, m::Assgn; cat) = 
  all(eval_boolexpr(x, g, m; cat) for x in c.exprs)
eval_boolexpr(c::BoolOr, g::CGraph, m::Assgn; cat) = 
  any(eval_boolexpr(x, g, m; cat) for x in c.exprs)

"""Check whether homs are equal by looping over domain."""
function eval_boolexpr(c::Commutes, ::CGraph, ms::Assgn; cat)
  paths = map(c.pths) do p 
    foldl(compose[cat], ms[p]) 
  end
  doms = dom.(paths)
  allequal(doms) || error("Paths should all have same domain")
  d, S = first(doms), acset_schema(first(doms))
  c.commutes == all(types(S)) do o
    𝒞 = entity_attr_cat(cat, o)
    all(parts(d, o)) do p
      p′ = o ∈ ob(S) ? p : Left(p)
      allequal([hom_map[𝒞](pth[o])(p′) for pth in paths])
    end
  end
end 

function eval_boolexpr(q::Quantifier, g::CGraph, curr::Assgn; cat)
  d, cd = [get_ob(g,x,curr) for x in [g[q.e, :src], g[q.e, :tgt]]]
  cands = []
  @debug "$(q.kind) ($(q.e))"
  monic = q.monic == true ? ob(acset_schema(d)) : q.monic
  for h in homomorphisms(d, cd; monic)
    x = deepcopy(curr)
    x[q.e] = h 
    @debug "candidate morphism $(components(h))"
    if eval_boolexpr(q.st, g, x; cat)
      @debug "successful candidate!"
      push!(cands, x)
    end
  end 
  n = length(cands)
  suc = [eval_boolexpr(q.expr, g, cand; cat) for cand in cands]
  n_success = sum([0, suc...])
  @debug "$(q.kind) ($(q.e)) n $n success $suc"
  if     q.kind == :Exists  return n_success > 0
  elseif q.kind == :Exists! return n_success == 1
  elseif q.kind == :Forall  return n_success == n
  end
end 


map_edges(f,c::BoolConst) = c
map_edges(f,c::BoolNot) = BoolNot(map_edges(f,c.expr))
map_edges(f,c::BoolAnd) = BoolAnd([map_edges(f,x) for x in c.exprs]...)
map_edges(f,c::BoolOr) = BoolOr([map_edges(f,x) for x in c.exprs]...)
map_edges(f,c::Commutes) = Commutes([f[:E].(p) for p in c.pths]...; commutes=c.commutes)
map_edges(f,c::Quantifier) = Quantifier(f[:E](c.e),c.kind,map_edges(f,c.expr); 
                                        st = map_edges(f,c.st),monic=c.monic)

# Constraint = CGraph × BoolExpr
################################
"""A constraint graph and a BoolExpr (which refers to the constraint graph)"""
@struct_hash_equal struct Constraint
  g::CGraph 
  d::BoolExpr 
  function Constraint(g,d)
    nparts(g,:VLabel) == 0 || error("No vertex variables allowed")
    nparts(g,:ELabel) == 0 || error("No edge variables allowed")
    # check that all of the object assignments match the defined morphisms 
    for (eind, (s, t, h)) in enumerate(zip(g[:src], g[:tgt], g[:elabel]))
      sv, tv = [g[x,:vlabel] for x in [s,t]]
      if h isa ACSetTransformation 
        dom(h) == sv && codom(h) == tv || error("Diagram not functorial: edge $eind")
      elseif isnothing(h) # h is filled by a quantifier. Src/Tgt must be defined
        for (i,v) in [(s,sv),(t,tv)]
          if !(v isa ACSet) 
            inc = vcat(incident(g, i, :src), incident(g,i,:tgt))
            err = "Edge $eind: undefined vertex $i for a quantifier in $g \n $d"
            any(e->g[e,:elabel] isa Int, inc) || error(err)
          end
        end 
      end # if a variable, no constraints until runtime
    end 
    # Check that the constraint is compatible with the graph
    ce = check_expr(g,d)
    isempty(ce) || error(join(ce,"\n"))

    return new(g,d)
  end 
end
arity(g::Constraint) = arity(g.g)

(F::Migrate)(c::Constraint) = Constraint(F(c.g),c.d)
sparsify(c::Constraint) = Constraint(sparsify(c.g), c.d)
const Trivial = Constraint(CGraph(), True)
const Trivial′ = Constraint(CGraph(), False)

"""
Combine two constraints conjunctively, sharing as much of the computation graph 
as possible (i.e. pushout along the maximum common subgraph)
"""
function ⊗(c1::Constraint,c2::Constraint) 
  if c1 == Trivial′ || c2 == Trivial′ return Trivial′ end 
  if c1 == Trivial  return c2 
  elseif c2 == Trivial return c1 
  end  

  new_g = merge_graphs(c1.g, c2.g)
  l1, l2 = legs(new_g)
  Constraint(apex(new_g), map_edges(l1,c1.d) ⊗ map_edges(l2,c2.d))
end

⊗(cs::Constraint...) = reduce(⊗, cs; init=Trivial) 

"""
Combine two constraints disjunctively, sharing as much of the computation graph 
as possible.
"""
function ⊕(c1::Constraint,c2::Constraint) 
  if c1 == Trivial || c2 == Trivial return Trivial end 
  if c1 == Trivial′  return c2 
  elseif c2 == Trivial′ return c1 
  end  
  new_g = merge_graphs(c1.g, c2.g)
  l1, l2 = legs(new_g)
  new_d = map_edges(l1,c1.d) ⊕ map_edges(l2,c2.d)
  Constraint(apex(new_g), new_d)
end

⊕(cs::Constraint...) = reduce(⊕, cs; init=Trivial′) 

¬(c::Constraint) = Constraint(c.g, ¬c.d)


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

function apply_constraint(c::Constraint, fs...; cat=nothing)
  # populate assignment of ACSetTransformations 
  ms = Assgn(map(enumerate(c.g[:elabel])) do (i, e) 
    if e isa ACSetTransformation 
      return e 
    elseif e isa Int # need to check that the argument typechecks
      f = fs[e]
      s, t = [c.g[i, [x, :vlabel]] for x in [:src,:tgt]]
      errs = "Edge $i: Bad src $s \n!=\n $(dom(f)) for arg $e"
      isnothing(s) || dom(f) == s || error(errs)
      errt = "Edge $i: Bad tgt $t \n!=\n $(codom(f)) for arg $e"
      isnothing(t) || codom(f) == t || error(errt)
      return f
    end # Assignment has "nothing" for variables that are quantified
  end)
  return eval_boolexpr(c.d, c.g, ms; cat)  # Evaluate expression
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
  cg = @acset CGraph begin V=3; E=3; src=[2,1,2]; tgt=[1,3,3];
    vlabel=[codom(f), dom(f), nothing]; elabel=[f, nothing, 1]
  end
  expr = ∃(2, Commutes([1,2],[3]); monic=monic)
  return Constraint(cg, pos ? expr : ¬(expr))
end

NAC(f; kw...) = AppCond(f, false; kw...)
PAC(f; kw...) = AppCond(f, true; kw...)

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
  cg = @acset CGraph begin V=4; E=5; src=[1,1,2,2,3]; tgt=[2,3,3,4,4]
    vlabel=[A,B,nothing,Y]; elabel=[vertical, nothing, nothing, bottom, 1]
  end
  expr = ∀(2, ∃(3, Commutes([1,3],[2]) ⊗ Commutes([3,5],[4]); 
                monic=monic_exists);
           st=Commutes([2,5],[1,4]), monic=monic_all)
  return Constraint(cg, expr)
end

# Visualize constraints
#######################

function to_graphviz(c::Constraint)
  pg = to_graphviz_property_graph(c.g; node_labels=true,
                                  graph_attrs=Dict(:label=>sprint(show, c.d)))

  for v in vertices(c.g)
    x = isnothing(c.g[v, :vlabel]) ? "λ" : ""
    set_vprop!(pg, v, :label, "$x$v")
  end

  for e in edges(c.g)
    x = if     c.g[e, :elabel] isa Int    "(λ$(c.g[e, :elabel]))"
        elseif isnothing(c.g[e, :elabel]) getquantifier(c.d, e)
        else                              ""
    end 
    set_eprop!(pg, e, :label, "$x$e")
  end
  to_graphviz(pg)
end

function getquantifier(d::BoolExpr, e::Int)
  if d isa Quantifier && d.e == e
    quantifier_symbol(d)
  else 
    qs = collect(filter(!isnothing, getquantifier.(subexprs(d), Ref(e))))
    isempty(qs) ? nothing : only(qs)
  end
end

end # module
