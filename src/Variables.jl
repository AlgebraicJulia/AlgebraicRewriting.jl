module Variables
export Var, CallDict, sub_vars, hasvar, FinDomDefaultDict

using Catlab, Catlab.CategoricalAlgebra, Catlab.Schemas
using Catlab.CategoricalAlgebra.Sets:  SetFunctionCallable, IdentityFunction
using Catlab.Theories: attr
import Catlab.CategoricalAlgebra: dom, codom
using Catlab.CategoricalAlgebra.CSets: type_components

using StructEquality

# Variables and FinDom functions that specify where variables go
################################################################
"""Wrapper type for variables"""
@struct_hash_equal struct Var
  sym::Symbol
end
Base.string(v::Var) = string(v.sym)


""" 
TODO: upstream to Catlab

Function in **Set** represented by a dictionary.
The domain is `TypeSet{S}` where `S` is the type of the 
dictionary's `keys` (which is a subtype of it values)
"""
@struct_hash_equal struct FinDomDefaultDict{K2,K<:K2,D<:AbstractDict{K,K2}} <:
    FinDomFunction{D,TypeSet{K},TypeSet{K2}}
  func::D
end
dom(::FinDomDefaultDict{K}) where {K} = TypeSet(K)
codom(::FinDomDefaultDict{K}) where {K} = TypeSet(K)
(f::FinDomDefaultDict{K})(x::K) where K = get(f.func, x, x)
force(f::FinDomDefaultDict) = f


# Variable substitution
#######################
"""Extract the mapping on variables from a LooseACSetTransformation"""
function get_var_maps(m::LooseACSetTransformation{S}) where S 
  is_natural(m) || error("unnatural m $m")
  d = Dict()
  for (atr,_,atyp) in attrs(S)
    for v in filter(x->x isa Var, dom(m)[atr])
      d[v.sym] = type_components(m)[atyp](v)
    end
  end
  return d
end

"""Substitute the dom and codom of an ACSetTransformation f """
function sub_vars(f::ACSetTransformation, d::AbstractDict)
  old_comps = collect(pairs(type_components(f)))
  new_comps = Dict(map(old_comps) do (k,v)
    new_v = sub_vars(v, d)
    return k => new_v
  end)
  new_d = sub_vars(dom(f),d)
  new_cd = sub_vars(codom(f),d)
  if any(x->!(x isa IdentityFunction), values(new_comps))
    return LooseACSetTransformation(f.components,new_comps, new_d, new_cd)
  else 
    return ACSetTransformation(new_d,new_cd; f.components...)
  end
end
# sub_vars(f::TightACSetTransformation, _::ACSetTransformation) = f
# sub_vars(f::TightACSetTransformation, _::AbstractDict) =  f
sub_vars(f::ACSetTransformation, m::ACSetTransformation) = 
  sub_vars(f, get_var_maps(m)) 


"""
Given a match morphism m which binds some subset of variables 
in X, apply the substitutions to the attributes in X.
"""
function sub_vars(X_::StructACSet{S}, d::AbstractDict) where S

  X = deepcopy(X_)
  Attr = attrs(S; just_names=true)
  for aname in Attr
    set_subpart!(X, aname, [sub_vars(x, d) for x in X[aname]])
  end
  X
end
sub_vars(X::StructACSet, m::ACSetTransformation) = sub_vars(X, get_var_maps(m)) 

sub_vars(v::Var, vs::AbstractDict) = get(vs, v.sym, v)
function sub_vars(f::FinDomDefaultDict{K2,K,D}, vs::AbstractDict) where {K2,K,D}
  ndict = Dict(map(collect(f.func)) do (k,v)
    sub_vars(k,vs) => sub_vars(v,vs)
  end)
  if K == K2 && !any(kv->kv[1]!=kv[2], collect(ndict))
    return IdentityFunction(TypeSet(K))
  else 
    return FinDomDefaultDict{K2,K,D}(ndict)
  end
end
sub_vars(v::Any, _::AbstractDict) = v

function sub_vars(x::Expr, vs::AbstractDict)
  for (k, v) in pairs(vs)
    kk = Meta.parse(string(k))
    rep!(x, kk, v)
  end
  return hasvar(x) ? x : eval(x)
end


"""Replace old with new in an expression recursively"""
function rep!(e, old, new)
  for (i,a) in enumerate(e.args)
    if a==old
      e.args[i] = new
    elseif a isa Expr
      rep!(a, old, new)
    end # otherwise do nothing
  end
  e
end


"""Check if any attribute has a variable"""
function hasvar(s::StructACSet{S}) where S
  any(map(attr(S)) do a
    any(x->x isa Var, s[a])
  end)
end

hasvar(s::Slice) = hasvar(dom(s.slice))

"""Does this expression contain a Var() object in it"""
function hasvar(e) # Expr
  if e isa Expr 
    if length(e.args) > 1 && first(e.args) == :Var 
      return true 
    else 
      return any(hasvar, e.args) 
    end
  else
    return false
  end
end

end # module
