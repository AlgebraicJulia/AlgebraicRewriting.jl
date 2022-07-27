module Search
export homomorphism, homomorphisms, is_homomorphic, is_isomorphic

using Base.Meta: quot

using Catlab, Catlab.Theories
using Catlab.Theories: SchemaDescType, attr, adom, acodom
using Catlab.CategoricalAlgebra: ACSet, StructACSet, ACSetTransformation,LooseACSetTransformation, nparts, parts, subpart
using Catlab.CategoricalAlgebra.CSets: map_components
using Catlab.CategoricalAlgebra.CSetDataStructures: SchemaDescType
using ..Variables

# Backtracking search
#--------------------

""" Algorithm for finding homomorphisms between attributed ``C``-sets.
"""
abstract type ACSetHomomorphismAlgorithm end

""" Find attributed ``C``-set homomorphisms using backtracking search.

This procedure uses the classic backtracking search algorithm for a
combinatorial constraint satisfaction problem (CSP). As is well known, the
homomorphism problem for relational databases is reducible to CSP. Since the
C-set homomorphism problem is "the same" as the database homomorphism problem
(insofar as attributed C-sets are "the same" as relational databases), it is
also reducible to CSP. Backtracking search for CSP is described in many computer
science textbooks, such as (Russell & Norvig 2010, *Artificial Intelligence*,
Third Ed., Chapter 6: Constraint satisfaction problems, esp. Algorithm 6.5). In
our implementation, the search tree is ordered using the popular heuristic of
"minimum remaining values" (MRV), also known as "most constrained variable.
"""
struct BacktrackingSearch <: ACSetHomomorphismAlgorithm end

""" Find attributed ``C``-set homomorphisms using a conjunctive query.

This algorithm evaluates a conjunctive query (limit in `FinSet`) to find all
homomorphisms between two ``C``-sets. In fact, conjunctive queries are exactly
the *representable* functors from ``C``-sets to sets, so every conjunctive query
arises in this way, with the caveat that conjunctive queries may correspond to
to infinite ``C``-sets when ``C`` is infinite (but possibly finitely presented).
"""
struct HomomorphismQuery <: ACSetHomomorphismAlgorithm end

""" Find a homomorphism between two attributed ``C``-sets.

Returns `nothing` if no homomorphism exists. For many categories ``C``, the
``C``-set homomorphism problem is NP-complete and thus this procedure generally
runs in exponential time. It works best when the domain object is small.

To restrict to *monomorphisms*, or homomorphisms whose components are all
injective functions, set the keyword argument `monic=true`. To restrict only
certain components to be injective or bijective, use `monic=[...]` or
`iso=[...]`. For example, setting `monic=[:V]` for a graph homomorphism ensures
that the vertex map is injective but imposes no constraints on the edge map.

To restrict the homomorphism to a given partial assignment, set the keyword
argument `initial`. For example, to fix the first source vertex to the third
target vertex in a graph homomorphism, set `initial=(V=Dict(1 => 3),)`.

Use the keyword argument `alg` to set the homomorphism-finding algorithm. By
default, a backtracking search algorithm is used ([`BacktrackingSearch`](@ref)).

See also: [`homomorphisms`](@ref), [`isomorphism`](@ref).
"""
homomorphism(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  homomorphism(X, Y, alg; kw...)

function homomorphism(X::ACSet, Y::ACSet, alg::BacktrackingSearch; kw...)
  result = nothing
  backtracking_search(X, Y; kw...) do α
    result = α; return true
  end
  result
end

""" Find all homomorphisms between two attributed ``C``-sets.

This function is at least as expensive as [`homomorphism`](@ref) and when no
homomorphisms exist, it is exactly as expensive.
"""
homomorphisms(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  homomorphisms(X, Y, alg; kw...)

function homomorphisms(X::StructACSet{S}, Y::StructACSet{S},
                       alg::BacktrackingSearch; kw...) where {S}
  results = ACSetTransformation{S}[]
  backtracking_search(X, Y; kw...) do α
    push!(results, map_components(deepcopy, α)); return false
  end
  results
end

""" Is the first attributed ``C``-set homomorphic to the second?

This function generally reduces to [`homomorphism`](@ref) but certain algorithms
may have minor optimizations.
"""
is_homomorphic(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  is_homomorphic(X, Y, alg; kw...)

is_homomorphic(X::ACSet, Y::ACSet, alg::BacktrackingSearch; kw...) =
  !isnothing(homomorphism(X, Y, alg; kw...))

""" Find an isomorphism between two attributed ``C``-sets, if one exists.

See [`homomorphism`](@ref) for more information about the algorithms involved.
"""
isomorphism(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  isomorphism(X, Y, alg; kw...)

isomorphism(X::ACSet, Y::ACSet, alg::BacktrackingSearch; initial=(;)) =
  homomorphism(X, Y, alg; iso=true, initial=initial)

""" Find all isomorphisms between two attributed ``C``-sets.

This function is at least as expensive as [`isomorphism`](@ref) and when no
homomorphisms exist, it is exactly as expensive.
"""
isomorphisms(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  isomorphisms(X, Y, alg; kw...)

isomorphisms(X::ACSet, Y::ACSet, alg::BacktrackingSearch; initial=(;)) =
  homomorphisms(X, Y, alg; iso=true, initial=initial)

""" Are the two attributed ``C``-sets isomorphic?

This function generally reduces to [`isomorphism`](@ref) but certain algorithms
may have minor optimizations.
"""
is_isomorphic(X::ACSet, Y::ACSet; alg=BacktrackingSearch(), kw...) =
  is_isomorphic(X, Y, alg; kw...)

is_isomorphic(X::ACSet, Y::ACSet, alg::BacktrackingSearch; kw...) =
  !isnothing(isomorphism(X, Y, alg; kw...))

""" Internal state for backtracking search for ACSet homomorphisms.
"""
struct BacktrackingState{S <: SchemaDescType,
    Assign <: NamedTuple, PartialAssign <: NamedTuple, LooseFun <: NamedTuple,
    InvParts <: NamedTuple,
    Dom <: StructACSet{S}, Codom <: StructACSet{S}, VAssign <: NamedTuple}
  """ The current assignment, a partially-defined homomorphism of ACSets. """
  assignment::Assign
  """ Depth in search tree at which assignments were made. """
  assignment_depth::Assign
  """ Inverse assignment for monic components or if finding a monomorphism. """
  inv_assignment::PartialAssign
  """ Parition of domain for purposes of inverse assignment"""
  inv_parts::InvParts
  """ Domain ACSet: the "variables" in the CSP. """
  dom::Dom
  """ Codomain ACSet: the "values" in the CSP. """
  codom::Codom
  type_components::LooseFun
  var_assign::VAssign
end


function backtracking_search(f, X::StructACSet{S}, Y::StructACSet{S};
  monic=false, iso=false, type_components=(;), initial=(;),
  bindvars=false, init_check=true) where {Ob, Hom, Attr, S<:SchemaDescType{Ob,Hom,Attr}}
  # Fail early if no monic/isos exist on cardinality grounds.
  if iso isa Bool
    iso = iso ? Ob : ()
  end
  for c in iso
    if monic isa Bool
      monic = true
    elseif monic isa AbstractVector
      push!(monic, c)
    elseif monic isa Dict
      monic[c] = ones(Int, nparts(X,c))
    end
    nparts(X,c) == nparts(Y,c) || return false
  end

  if monic isa Bool
    monic = monic ? Ob : ()
  end
  if monic isa AbstractVector || monic isa Tuple
    monic = Dict([o=>ones(Int,nparts(X, o)) for o in monic])
  elseif monic isa Dict
    for (k,v) in collect(monic)
      if isempty(v)
        delete!(monic,k)
      else
      sort(collect(Set(v))) == 1:maximum(v) || error("monic not a partition")
      end
    end
  elseif !(monic isa Dict)
    error("typeof monic $(typeof(monic))")
  end
  # no init_check is a special case of a partitioned inv_assignment
  # Where everything that has been initialized gets a unique part
  if !init_check
    for (k,v) in collect(pairs(initial))
      error("TODO")
    end
  end

  # Injections between finite sets are bijections, so reduce to that case.
  #monic = unique([iso..., monic...])
  for (c,v) in collect(monic)
    if !isempty(v) && haskey(initial, c)
      nmax = maximum([count(==(i), v) for i in 1:maximum(v)])
      nmax <= nparts(Y,c) || return false
    end
  end

  # Initialize state variables for search.
  assignment = NamedTuple{Ob}(zeros(Int, nparts(X, c)) for c in Ob)
  assignment_depth = map(copy, assignment)
  inv_assignment = NamedTuple{Ob}(
  ((haskey(monic,c) && !isempty(monic[c]) ? zeros(
      Int, (nparts(Y, c), maximum(monic[c]))) : nothing) for c in Ob))
  loosefuns = NamedTuple{Attr}(
    isnothing(type_components) ? identity : get(
      type_components, c, identity) for c in Attr)

  # Get variables
  d = Dict{Symbol, Union{Nothing, Dict}}([x=>Dict() for x in Attr])
  map(zip(attr(S), acodom(S))) do (f, D)
    if !bindvars || !(haskey(d,D)  || any(v->v isa Var, X[f]))
        d[D] = nothing
    end
    map(filter(v->v isa Var, X[f])) do (v)
      if !isnothing(d[D])
          d[D][v] = (0, nothing)
      end
    end
  end
  vassign = NamedTuple{Attr}([d[a] for a in Attr])
  state = BacktrackingState(assignment, assignment_depth, inv_assignment, NamedTuple(monic), X, Y,
  loosefuns, vassign)

  # Make any initial assignments, failing immediately if inconsistent.
  for (c, c_assignments) in pairs(initial)
    for (x, y) in partial_assignments(c_assignments)
      assign_elem!(state, 0, Val{c}, x, y) || return false
    end
  end

  # Start the main recursion for backtracking search.
  backtracking_search(f, state, 1)
end


function backtracking_search(f, state::BacktrackingState{S}, depth::Int) where {S}
  # Choose the next unassigned element.
  mrv, mrv_elem = find_mrv_elem(state, depth)
  if isnothing(mrv_elem)
    # No unassigned elements remain, so we have a complete assignment.
    if any(!=(identity), state.type_components)
      return f(LooseACSetTransformation{S}(
      state.assignment, state.type_components, state.dom, state.codom))
    elseif any(x->!isnothing(x) && !isempty(x), state.var_assign)
      va = Dict([k=> CallDict(Dict([k_=>v_ for (k_, (_,v_)) in collect(v)]))
      for (k, v) in pairs(state.var_assign) if !isnothing(v)])
      return f(LooseACSetTransformation(state.assignment, va, state.dom, state.codom))
      else
      return f(ACSetTransformation(state.assignment, state.dom, state.codom))
      end
    elseif mrv == 0
    # An element has no allowable assignment, so we must backtrack.
    return false
  end
  c, x = mrv_elem

  # Attempt all assignments of the chosen element.
  Y = state.codom
  for y in parts(Y, c)
  assign_elem!(state, depth, Val{c}, x, y) &&
  backtracking_search(f, state, depth + 1) &&
  return true
  unassign_elem!(state, depth, Val{c}, x)
  end
  return false
end

""" Find an unassigned element having the minimum remaining values (MRV).
"""
function find_mrv_elem(state::BacktrackingState{S}, depth) where S
  mrv, mrv_elem = Inf, nothing
  Y = state.codom
  for c in ob(S), (x, y) in enumerate(state.assignment[c])
    y == 0 || continue
    n = count(can_assign_elem(state, depth, Val{c}, x, y) for y in parts(Y, c))
    if n < mrv
      mrv, mrv_elem = n, (c, x)
    end
  end
  (mrv, mrv_elem)
end

""" Check whether element (c,x) can be assigned to (c,y) in current assignment.
"""
function can_assign_elem(state::BacktrackingState, depth,::Type{Val{c}}, x, y) where c
  # Although this method is nonmutating overall, we must temporarily mutate the
  # backtracking state, for several reasons. First, an assignment can be a
  # consistent at each individual subpart but not consistent for all subparts
  # simultaneously (consider trying to assign a self-loop to an edge with
  # distinct vertices). Moreover, in schemas with non-trivial endomorphisms, we
  # must keep track of which elements we have visited to avoid looping forever.
  ok = assign_elem!(state, depth, Val{c}, x, y)
  unassign_elem!(state, depth, Val{c}, x)
  return ok
end

""" Attempt to assign element (c,x) to (c,y) in the current assignment.

Returns whether the assignment succeeded. Note that the backtracking state can
be mutated even when the assignment fails.
"""
@generated function assign_elem!(state::BacktrackingState{S}, depth,
      ::Type{Val{c}}, x, y) where {S, c}
  quote
    y′ = state.assignment.$c[x]
    y′ == y && return true  # If x is already assigned to y, return immediately.
    y′ == 0 || return false # Otherwise, x must be unassigned.
    if (!isnothing(state.inv_assignment.$c)
        && state.inv_assignment.$c[y, state.inv_parts[c][x]] != 0)
      # Also, y must unassigned in the inverse assignment.
      return false
    end

  # Check attributes first to fail as quickly as possible.
  X, Y = state.dom, state.codom
  $(map(zip(attr(S), adom(S), acodom(S))) do (f, c_, d)
    :($(quot(c_))!=c
      ||(subpart(X,x,$(quot(f))) isa Var && !isnothing(state.var_assign[$(quot(d))])
      && (state.var_assign[$(quot(d))][subpart(X,x,$(quot(f)))][1] == 0
      ||(state.var_assign[$(quot(d))][subpart(X,x,$(quot(f)))][2] == subpart(Y,y,$(quot(f)))) ))
      || state.type_components[$(quot(d))](subpart(X,x,$(quot(f))))
      == subpart(Y,y,$(quot(f))) || return false)
  end...)

  # Make the assignment and recursively assign subparts.
  state.assignment.$c[x] = y
  state.assignment_depth.$c[x] = depth
  if !isnothing(state.inv_assignment.$c)
    state.inv_assignment.$c[y, state.inv_parts[c][x]] = x
  end
  $(map(zip(attr(S), adom(S), acodom(S))) do (f, c_, d)
  :(if ($(quot(c_))==c
    && subpart(X,x,$(quot(f))) isa Var
    && !isnothing(state.var_assign[$(quot(d))]))
      state.var_assign[$(quot(d))][subpart(X,x,$(quot(f)))]=(
      state.var_assign[$(quot(d))][subpart(X,x,$(quot(f)))][1]+1,subpart(Y,y,$(quot(f))))
  end)
  end...)

  $(map(out_hom(S, c)) do (f, d)
    :(assign_elem!(state, depth, Val{$(quot(d))}, subpart(X,x,$(quot(f))),
    subpart(Y,y,$(quot(f)))) || return false)
  end...)

  return true
  end
end

""" Unassign the element (c,x) in the current assignment.
"""
@generated function unassign_elem!(state::BacktrackingState{S}, depth,
        ::Type{Val{c}}, x) where {S, c}
quote
  state.assignment.$c[x] == 0 && return
  assign_depth = state.assignment_depth.$c[x]
  @assert assign_depth <= depth
  if assign_depth == depth
    X = state.dom

    if !isnothing(state.inv_assignment.$c)
      y = state.assignment.$c[x]
      state.inv_assignment.$c[y, state.inv_parts[c][x]] = 0
    end
    $(map(zip(attr(S), adom(S), acodom(S))) do (f, c_, d)
    :(if ($(quot(c_))==c && !isnothing(state.var_assign[$(quot(d))])
      && subpart(X,x,$(quot(f))) isa Var)
      state.var_assign[$(quot(d))][subpart(X,x,$(quot(f)))]=(
      state.var_assign[$(quot(d))][subpart(X,x,$(quot(f)))][1]-1,
      state.var_assign[$(quot(d))][subpart(X,x,$(quot(f)))][2])
      end)
    end...)

    state.assignment.$c[x] = 0
    state.assignment_depth.$c[x] = 0
    $(map(out_hom(S, c)) do (f, d)
      :(unassign_elem!(state, depth, Val{$(quot(d))},
      subpart(X,x,$(quot(f)))))
    end...)
  end
end
end

""" Get assignment pairs from partially specified component of C-set morphism.
"""
partial_assignments(x::AbstractDict) = pairs(x)
partial_assignments(x::AbstractVector) =
((i,y) for (i,y) in enumerate(x) if !isnothing(y) && y > 0)

# FIXME: Should these accessors go elsewhere?
in_hom(S, c) = [dom(S,f) => f for f in hom(S) if codom(S,f) == c]
out_hom(S, c) = [f => codom(S,f) for f in hom(S) if dom(S,f) == c]



end # module