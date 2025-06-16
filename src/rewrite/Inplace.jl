module Inplace
export compile_rewrite, RewriteProgram, rewrite!, rewrite_match!

using MLStyle
using ACSets
using ACSets.DenseACSets: attrtype_type
using Catlab.BasicSets, Catlab.CategoricalAlgebra
using ..Utils
import ..Utils: rewrite_match_maps

# This module provides a bytecode to compile a rewrite rule into which can be
# interpreted to perform the rewrite in place.

@data Reference begin
  # a register in the Machine used to store IDs of newly-added parts
  Reg(idx::Int)
  # A match morphism L->G allows us to refer to parts of G via parts of L
  HomValue(type::Symbol, idx::Int)
end

@data AttrVal begin
  Const(val::Any)
  AttrReg(idx::Int)
end

@data AttrRegInit begin
  Compute(f::Function)
  Fresh()
end

@data RewriteInst begin
  # Add a new part of type `type` to the acset, and put the id of the new part
  # into `reg`
  Add(type::Symbol, reg::Reg)

  # Remove a part
  Del(part::HomValue)

  # Set the value of the morphism `f` on a newly-added `part` to `value`
  SetHom(part::Reg, value::Reference, f::Symbol)

  # Set the value of `f` on the attribute `f` on `part` to `value`
  SetAttr(part::Reference, value::AttrVal, f::Symbol)

  InitAttrReg(reg::AttrReg, attrtype::Symbol, value::AttrRegInit)
end

struct Machine
  regvals::Vector{Int}
  attr_regvals::Vector{Any}
end

Base.getindex(m::Machine, r::Reg) = m.regvals[r.idx]
Base.getindex(m::Machine, r::AttrReg) = m.attr_regvals[r.idx]

Base.setindex!(m::Machine, i::Int, r::Reg) = (m.regvals[r.idx] = i)
Base.setindex!(m::Machine, x::Any, r::AttrReg) = (m.attr_regvals[r.idx] = x)

const Referable = Union{Reference, AttrReg}

function lookup(m::Machine, hom::NamedTuple, r::Referable)
  @match r begin
    Reg(_) => m[r]
    AttrReg(_) => m[r]
    HomValue(type, i) => hom[type](i)
  end
end

const Assignment = Dict{Tuple{Symbol, Int}, Referable}

struct RewriteProgram
  regs::Int
  attr_regs::Int
  adds::Vector{Add}
  inits::Vector{InitAttrReg}
  set_homs::Vector{SetHom}
  set_attrs::Vector{SetAttr}
  dels::Vector{Del}
  hom_template::Vector{Tuple{Symbol, Vector{Referable}}}
end

Base.show(io::IO, r::Reg) = print(io, "[$(r.idx)]")
Base.show(io::IO, r::Add) = print(io, "$(r.reg) = new($(r.type))")
Base.show(io::IO, r::AttrReg) = print(io, "{$(r.idx)}")
Base.show(io::IO, r::Compute) = print(io, r.f)
Base.show(io::IO, r::Union{SetAttr,SetHom}) = print(io, "$(r.part).$(r.f)=$(r.value)")
Base.show(io::IO, r::Del) = print(io, "Del($(r.part))")
Base.show(io::IO, r::HomValue) = print(io, "$(r.type)$(r.idx)")
Base.show(io::IO, r::InitAttrReg) = print(io, "$(r.reg) = $(r.value)($(r.attrtype))")
Base.show(io::IO, m::Machine) = println(io, "Machine($(m.regvals), $(m.attr_regvals))")

function Base.show(io::IO, r::RewriteProgram)
  println(io, "$(r.regs) regs, $(r.attr_regs) attr_regs")
  println(io, "Adds: $(join(r.adds,","))")
  println(io, "inits: $(join(r.inits,","))")
  println(io, "set_homs: $(join(r.set_homs,","))")
  println(io, "set_attrs: $(join(r.set_attrs,","))")
  println(io, "dels: $(join(r.dels,","))")
  println(io, "hom_template:\n\t$(join(["$x: " * join(sprint.(show, y), ",")
                                     for (x, y) in r.hom_template],"\n\t"))")
end

function interp_program!(prog::RewriteProgram, hom::NamedTuple, 
                         state::ACSet{<:MarkAsDeleted}, 
                         m::Union{Nothing, Machine}=nothing)
  if isnothing(m)
    m = Machine(
      zeros(Int, prog.regs),
      zeros(Missing, prog.attr_regs)
    )
  end
  for inst in prog.adds
    m[inst.reg] = add_part!(state, inst.type)
  end
  for inst in prog.inits
    fdf = get(hom[inst.attrtype])
    vals = [getvalue(fdf(v)) for v in sort(collect(dom(fdf)))]
    m[inst.reg] = @match inst.value begin
      Fresh() => AttrVar(add_part!(state, inst.attrtype))
      Compute(f) => f(vals)
    end
  end
  for inst in prog.set_homs
    state[m[inst.part], inst.f] = lookup(m, hom, inst.value)
  end
  for inst in prog.set_attrs
    x = @match inst.value begin
      Const(val) => val
      AttrReg(_) => m[inst.value]
    end
    state[lookup(m, hom, inst.part), inst.f] = x
  end
  for inst in prog.dels
    rem_part!(state, inst.part.type, hom[inst.part.type](inst.part.idx))
  end
  NamedTuple(map(prog.hom_template) do (x, v) 
    T = x ∈ ob(acset_schema(state)) ? Int : Union{AttrVar, attrtype_type(state, x)}
    x => T[lookup(m, hom, r) for r in v]
  end)
end

"""
assignment allows us to 
- set attributes to things that were matched by original hom search
"""
struct Compiler
  next_reg::Ref{Int}
  next_attr_reg::Ref{Int}
  assignment::Assignment
  function Compiler()
    new(Ref(1), Ref(1), Assignment())
  end
end

function assign!(c::Compiler, ob::Symbol, part::Int)
  reg = Reg(c.next_reg[])
  c.next_reg[] += 1
  c.assignment[(ob, part)] = reg
  reg
end

function assign_av!(c::Compiler, attrtype::Symbol, part::Int)
  reg = AttrReg(c.next_attr_reg[])
  c.next_attr_reg[] += 1
  c.assignment[(attrtype, part)] = reg
  reg
end

function add(::Rule, c::Compiler, ob::Symbol, part::Int)
  reg = assign!(c, ob, part)
  Add(ob, reg)
end

function init(r::Rule, c::Compiler, attrtype::Symbol, var::Int)
  preim = preimage(right(r)[attrtype], Left(var))

  initializer = if var ∈ keys(r.exprs[attrtype])
    isempty(preim) || error("Cannot give expr to preserved variable")
    Compute(r.exprs[attrtype][var])
  elseif !isempty(preim)
    Compute(vs -> vs[get(left(r)[attrtype])(only(preim)).val])
  else
    # Fresh()
    error(
      "Cannot create fresh variables, because for now we require that we" *
      "only rewrite acsets without variables"
    )
  end
  InitAttrReg(assign_av!(c, attrtype, var), attrtype, initializer)
end

function set_hom(r::Rule, c::Compiler, ob::Symbol, f::Symbol, fcodom::Symbol, i::Int)
  SetHom(c.assignment[(ob, i)], c.assignment[(fcodom, codom(r.R)[i, f])], f)
end

"""
Record how to set f(ob#i)
"""
function set_attr(r::Rule, c::Compiler, ob::Symbol, f::Symbol, fcodom::Symbol, i::Int)
  attr_val = @match codom(r.R)[i, f] begin
    v::AttrVar => begin
      c.assignment[(fcodom, v.val)]
    end
    x::Any => Const(x)
  end
  SetAttr(c.assignment[(ob, i)], attr_val, f)
end

function del(::Rule, ::Compiler, ob::Symbol, i::Int)
  Del(HomValue(ob, i))
end

function compile_rewrite(r::Rule{:DPO}; cat=nothing)
  cat = isnothing(cat) ? infer_acset_cat(codom(left(r))) : cat
  is_monic[cat](r.L) && is_monic[cat](r.R) ||
    error("both sides of rule must be monic in order to compile")

  c = Compiler()

  schema = acset_schema(dom(r.L))

  L_hit = Dict(ob => BitSet() for ob in objects(schema))
  R_hit = Dict(ob => BitSet() for ob in objects(schema))

  for ob in objects(schema)
    for i in parts(dom(r.L), ob)
      push!(L_hit[ob], r.L.components[ob](i))
      push!(R_hit[ob], r.R.components[ob](i))
      c.assignment[(ob, r.R.components[ob](i))] = HomValue(ob, r.L.components[ob](i))
    end
  end

  # A part is added if it appears in the R but does not appear in I
  adds = [
    add(r, c, ob, i)
    for ob in objects(schema)
      for i in parts(codom(r.R), ob)
        if !(i ∈ R_hit[ob])
          ]
  # 
  inits = [
    init(r, c, attrtype, i)
    for attrtype in attrtypes(schema)
      for i in parts(codom(r.R), attrtype)
  ]

  set_homs = [
    set_hom(r, c, ob, f, fcodom, i)
    for ob in objects(schema)
      for (f,_,fcodom) in homs(schema; from=ob)
        for i in parts(codom(r.R), ob)
          if !(i ∈ R_hit[ob])
            ]

  set_attrs = [
    set_attr(r, c, ob, f, fcodom, i)
    for ob in objects(schema)
      for (f, _, fcodom) in attrs(schema; from=ob)
        for i in parts(codom(r.R), ob)
            ]
  # A part is deleted if it appears in L but not hit by the map I -> L
  dels = [
    del(r, c, ob, i)
    for ob in objects(schema)
      for i in parts(codom(r.L), ob)
        if !(i ∈ L_hit[ob])
          ]

  template = [
    (x, [c.assignment[(x,i)] for i in parts(codom(r.R), x)])
    for x in [objects(schema); attrtypes(schema)]
      ]

  RewriteProgram(
    c.next_reg[]-1,
    c.next_attr_reg[]-1,
    adds,
    inits,
    set_homs,
    set_attrs,
    dels,
    template
  )
end


"""
Apply a DPO rewrite to a specific match morphism. This will modify the codom
of the match morphism and returns a map from the R of the rule into the result.
"""
function rewrite_match!(r::Rule{:DPO}, m::ACSetTransformation; cat, prog=nothing)
  prog = isnothing(prog) ? compile_rewrite(r; cat) : prog
  res_comps = interp_program!(prog, components(m), codom[cat](m))
  ACSetTransformation(res_comps, codom[cat](right(r)), codom[cat](m); cat)
end

rewrite_match!(r::Rule{:DPO}, ::Nothing; kw...) = nothing

rewrite!(r::Rule{:DPO}, G; cat, initial=(;), random=false, kw...) =
  rewrite_match!(r, get_match(r, G; initial, random, cat); cat, kw...)

end
