module Inplace
export compile_rewrite, interp_program!, RewriteProgram

using MLStyle
using ACSets
using Catlab.CategoricalAlgebra
using ..Utils
import ..Utils: rewrite_match_maps

# This module provides a bytecode to compile a rewrite rule into which can be
# interpreted to perform the rewrite in place.
#
# Strategy for rewriting attributes

@data Reference begin
  Reg(idx::Int)
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

  # Set the value of the morphism `f` on `part` to `value`
  SetHom(part::Reg, value::Reference, f::Symbol)

  # Set the value of `f` on the attribute `f` on `part` to `value`
  SetAttr(part::Reg, value::AttrVal, f::Symbol)

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

function lookup(m::Machine, hom::NamedTuple, r::Reference)
  @match r begin
    Reg(_) => m[r]
    HomValue(type, i) => hom[type](i)
  end
end

struct RewriteProgram
  regs::Int
  attr_regs::Int
  adds::Vector{Add}
  inits::Vector{InitAttrReg}
  set_homs::Vector{SetHom}
  set_attrs::Vector{SetAttr}
  dels::Vector{Del}
end

function interp_program!(
  prog::RewriteProgram, hom::NamedTuple, state::ACSet, m::Union{Nothing, Machine}=nothing
)
  if isnothing(m)
    m = Machine(
      zeros(Int, prog.regs),
      zeros(Int, prog.attr_regs)
    )
  end
  for inst in prog.adds
    m[inst.reg] = add_part!(state, inst.type)
  end
  for inst in prog.inits
    m[inst.reg] = @match inst.value begin
      Fresh() => AttrVar(add_part!(state, inst.attrtype))
      Compute(f) => f(hom[inst.attrtype].fun.func)
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
    state[m[inst.part], inst.f] = x
  end
  for inst in prog.dels
    rem_part!(state, inst.part.type, hom[inst.part.type](inst.part.idx))
  end
end

struct Compiler
  next_reg::Ref{Int}
  next_attr_reg::Ref{Int}
  assignment::Dict{Tuple{Symbol, Int}, Union{Reference, AttrVal}}
  function Compiler()
    new(Ref(1), Ref(1), Dict{Tuple{Symbol, Int}, Union{Reference, AttrVal}}())
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

function add(r::Rule, c::Compiler, ob::Symbol, part::Int)
  reg = assign!(c, ob, part)
  Add(ob, reg)
end

function init(r::Rule, c::Compiler, attrtype::Symbol, var::Int)
  initializer = if var ∈ keys(r.exprs[attrtype])
     Compute(r.exprs[attrtype][var])
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

function set_attr(r::Rule, c::Compiler, ob::Symbol, f::Symbol, fcodom::Symbol, i::Int)
  attr_val = @match codom(r.R)[i, f] begin
    v::AttrVar => begin
      c.assignment[(fcodom, v.val)]
    end
    x::Any => Const(x)
  end
  SetAttr(c.assignment[(ob, i)], attr_val, f)
end

function del(r::Rule, c::Compiler, ob::Symbol, i::Int)
  Del(HomValue(ob, i))
end

function compile_rewrite(r::Rule{:DPO})
  is_monic(r.L) && is_monic(r.R) ||
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

  adds = [
    add(r, c, ob, i)
    for ob in objects(schema)
      for i in parts(codom(r.R), ob)
        if !(i ∈ R_hit[ob])
          ]

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
      for (f,_,fcodom) in attrs(schema; from=ob)
        for i in parts(codom(r.R), ob)
          if !(i ∈ R_hit[ob])
            ]

  dels = [
    del(r, c, ob, i)
    for ob in objects(schema)
      for i in parts(codom(r.L), ob)
        if !(i ∈ L_hit[ob])
          ]

  RewriteProgram(c.next_reg[], c.next_attr_reg[], adds, inits, set_homs, set_attrs, dels)
end

end
