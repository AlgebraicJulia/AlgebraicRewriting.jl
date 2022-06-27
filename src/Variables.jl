module Variables
export Var, CallDict, sub_vars, hasvar

using Catlab, Catlab.CategoricalAlgebra
using Catlab.Theories: attr

using AutoHashEquals

@auto_hash_equals struct Var
  sym::Symbol
end

Base.string(v::Var) = string(v.sym)

@auto_hash_equals struct CallDict <: Function
  d::Dict{Var,Any}
end
(f::CallDict)(v::Var) = f.d[v]
(f::CallDict)(x::Any) = x

# Variable substitution
#######################
function sub_vars(f::ACSetTransformation, m::LooseACSetTransformation)
  ACSetTransformation(sub_vars(dom(f),m), sub_vars(codom(f),m); f.components...)
end


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

function sub_vars(X::StructACSet, m::LooseACSetTransformation)
  X = deepcopy(X)
  as = acset_schema(dom(m))
  d = merge([v.func.d for v in values(m.type_components)]...)
  for aname in as.attrs
    set_subpart!(X, aname, [sub_vars(x, d) for x in X[aname]])
  end
  X
end


sub_vars(v::Var, vs::AbstractDict) = get(vs, v, v)
function sub_vars(x::Expr, vs::AbstractDict)
  for (k, v) in pairs(vs)
    kk = Meta.parse(string(k))
    rep!(x, kk, v)
  end
  return eval(x)
end

sub_vars(v::Any, _::AbstractDict) = v

function hasvar(s::StructACSet{S}) where S
  any(map(attr(S)) do a
    any(x->x isa Var, s[a])
  end)
end

end # module