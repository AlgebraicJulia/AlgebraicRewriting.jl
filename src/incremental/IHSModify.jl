module IHSModify

using DataStructures
using Catlab

using ...CategoricalAlgebra.CSets: invert_iso
using ..Algorithms: connected_acset_components, all_epis
import ..IHSData: IHS
using ..IHSAccess: pattern_cc, empty_profile, qrules, subobj_incl


# Constructing an IHS
#####################
function IHS(X::ACSet) 
  x = IHS()
  add_pattern!(x, X)
  x
end

function IHS(X::ACSet, f::ACSetTransformation, G::ACSet)
  ihs = IHS()
  add_pattern!(ihs, X)
  add_rule!(ihs, f)
  add_state!(ihs, G)
  ihs
end

function IHS(X::ACSet, f::Vector{<:ACSetTransformation}, G::ACSet)
  ihs = IHS()
  add_pattern!(ihs, X)
  add_rule!.(Ref(ihs), f)
  add_state!(ihs, G)
  ihs
end

# Simple mutations
##################

function inc_curr!(h::IHS, iₛ::Int) 
  h[iₛ, :curr] += 1
end

function set_state!(h::IHS, iₛ::Int, new_state::ACSet)
  h[iₛ, :state] = new_state
end

# Adding new compile-time data
##############################

"""
Add new pattern and set it up for each existing rule.
"""
function add_pattern!(ihs::IHS, pattern::ACSet)
  found = findfirst(==(pattern), ihs[:pattern])
  isnothing(found) || return found

  pattern_coprod, pattern_iso = connected_acset_components(pattern)
  add_pattern_cc!.(Ref(ihs), dom.(legs(pattern_coprod)))
  add_part!(ihs, :Pattern; pattern, pattern_iso, pattern_coprod)
end

"""
Add a new incremental pattern

Each subobject A ↣ X of a connected pattern X corresponds to a way of 
splitting X into "old" and "new" material. "A" is the old material (it is a 
true subobject) whereas the brand new material might not be a subobject (e.g.
we have added an edge between two existing vertices). ~A is our best approx 
to the new material: it includes the boundary ∂A of old and new.
"""
function add_pattern_cc!(ihs::IHS, pattern_cc::ACSet)
  found = findfirst(==(pattern_cc), ihs[:pattern_cc])
  isnothing(found) || return found
  iₚ = add_part!(ihs, :PatternCC; pattern_cc)
  _, sos = subobject_graph(pattern_cc);
  so_ids = map(enumerate(force.(hom.(sos)))) do (subpattern_idx, subobj)
    add_part!(ihs, :SubPattern; subpattern=iₚ, subobj, subpattern_idx)    
  end

  for i_rule in qrules(ihs)
    f = ihs[i_rule, :q]
    for (idata_iL, idata_iR, L, R) in subobj_rule_interactions3(f, pattern_cc)
      idata_L, idata_R = so_ids[[L,R]]
      add_part!(ihs, :Interaction; idata_iL, idata_iR, idata_L, idata_R, i_rule=iᵣ)
    end
  end

  dcs = alt_decomps(pattern_cc)
  for (iₛ, dc) in enumerate(dcs)
    for (decomp_colim, decomp_iso,  d, is_minimal) in dc 
      decomp = add_part!(ihs, :Decomp; decomp_tgt = so_ids[iₛ],
                          decomp_colim, decomp_iso, is_minimal)
      for (decomp_elem_idx, (v1,v2)) in enumerate(sort(d))
        decomp_elem_L, decomp_elem_R = so_ids[v1], so_ids[v2] 
        add_part!(ihs, :DecompElem; decomp, decomp_elem_L, decomp_elem_R, 
                  decomp_elem_idx)
      end
    end
  end

  iₚ
end

function add_rule!(ihs::IHS, rule::ACSetTransformation)
  found = findfirst(parts(ihs, :QRule)) do q 
    ihs[q,:profile] == empty_profile(ihs) || return false
    ihs[q,:rule] == rule
  end
  isnothing(found) || return found
  cat = infer_acset_cat(rule)
  iᵣ = add_part!(ihs, :Rule)
  for qL in reverse(all_epis(dom(rule)))
    _, qf = pushout[cat](rule, qL)
    profile = merge_profile(qL)
    q = add_part!(ihs, :QRule; profile, l_quot=qL, qrule=qf, rule=iᵣ)
    
    for p_cc in parts(ihs, :PatternCC)
      so_ids = incident(ihs, p_cc, :subpattern)
      X = ihs[p_cc, :pattern_cc]
      for (L, R, idata_iL, idata_iR) in subobj_rule_interactions3(qf, X)
        idata_L, idata_R = so_ids[[L,R]]
        add_part!(ihs, :Interaction; idata_iL, idata_iR, idata_L, idata_R, i_rule=q)
      end
    end
  end
  iᵣ
end


"""
Start tracking a new state with respect to all rule+pattern pairs.
"""
function add_state!(ihs::IHS, state::ACSet, i=nothing)
  iₛ = if isnothing(i) 
    add_part!(ihs, :State; state, curr=0)
  else 
    set_state!(ihs, i, state)
    ihs[i, :curr] = 0
    rem_parts!(ihs, :Update, incident(ihs, i, :update_state))
    ms = incident(ihs, i, :match_state)
    cms, ims = incident.(Ref(ihs), Ref(ms), [:created_match,:initial_match])
    rem_parts!.(Ref(ihs), [:CreatedMatch,:InitialMatch,:Match],
                [vcat(cms...),vcat(ims...),ms])
    i
  end

  for p in parts(ihs, :PatternCC)
    for match in components.(homomorphisms(pattern_cc(ihs, p), state))
      m = add_part!(ihs, :Match; match, match_time=0, match_state=iₛ)
      add_part!(ihs, :InitialMatch; initial_match=m, match_pattern=p)
    end
  end
  iₛ
end

# Helper functions
##################

""" 
What things were merged together by a morphism? Express this data as a 
Set of (Sets with 2+ elements) for each object in the schema 
"""
function merge_profile(f::ACSetTransformation)
  X, Y = dom(f), codom(f)
  Ob = ob(acset_schema(X))
  Dict(map(Ob) do o 
    d = Dict(p => Set{Int}() for p in parts(Y, o))
    for p in parts(X, o)
      push!(d[f[o](p)], p)
    end
    o => Set(filter(e->length(e)>1, collect(values(d))))
  end)
end

# Decompose a subobject (regarded as a task) into subtasks
##########################################################

subobj_equiv(a,b) = subobj_equiv(hom(a), hom(b))

subobj_equiv(a::ACSetTransformation,b::ACSetTransformation) = 
  any(isomorphisms(dom(a), dom(b))) do σ  
    force(compose[infer_acset_cat(a)](σ,b)) == force(a)
  end

function alt_decomps(X::ACSet)
  gr, sos = subobject_graph(X);
  esos = subobj_incl.(Ref(sos), gr[:src], gr[:tgt]) # edge monos
  [alt_decomps(gr, sos, esos, i) for i in 1:length(sos)]
end

"""
Given A ↣ X, all possible ways of expressing X as a colimit of diagrams of 
the form

  XL₁   ...  XLₙ
   ↓   ↘ ↓ ↙  ↓
   XR₁   A    XRₙ
"""
function alt_decomps(gr, sos::Vector, esos, iₐ::Int)
  res = Set{Tuple{Any,Any,Vector{Tuple{Int,Int}}, Bool}}()
  hsos = force.(hom.(sos))
  dsos = dom.(hsos)
  A =  hsos[iₐ] # subobject representing "old data"
  cat = infer_acset_cat(A)
  𝒞 = WithModel(cat)
  emp = sos[end] # empty subobject
  # All possible maps between subobjects where domain subobject ≤ A
  LRs = []
  for to_iₐ in incident(gr, iₐ, :tgt)
    L = src(gr, to_iₐ)
    for to_r in incident(gr, L, :src)
      R = tgt(gr, to_r)
      R == L && continue 
      R == iₐ && continue
      push!(LRs, (to_r, to_iₐ, L, R))
    end
  end
  queue = Set([Set([lr]) for lr in LRs])
  seen = Set{Set{Tuple{Int,Int,Int,Int}}}()

  while !isempty(queue)
    curr = pop!(queue)
    curr ∈ seen && continue 
    push!(seen, curr)
    curr_v = sort(collect(curr))

    ob1 = dsos[[L for (_,_,L,_) in curr_v]]
    ob2 = dsos[[iₐ; [R for (_,_,_,R) in curr_v]]]

    homs = vcat(map(enumerate(curr_v)) do (i, (LR, LA, L, R))
      [(esos[LA], i, 1), (esos[LR], i, i+1)] 
    end...)

    bpd = BipartiteFreeDiagram(ob1, ob2, homs)
  
    clim = colimit(𝒞, bpd)
    csp = Multicospan([A, getindex.(Ref(hsos), last.(curr_v))...])
    u = universal(𝒞, clim, csp) |> force
    is_monic(u) || continue # check if pushout is even a subobject
    out = findfirst(hom.(sos)) do so 
      any(isomorphisms(dom(u), dom(so))) do σ
        force(compose(𝒞, σ, so)) == u
      end
    end
    if out == 1
      Rs = sos[last.(curr_v)]
      min = all(1:length(Rs)) do i 
        no_i = filter(!=(i), 1:length(Rs))
        @withmodel cat (∨, ~) begin 
          subobj_equiv(Rs[i], ~foldl(∨, [sos[iₐ]; Rs[no_i]]; init=emp)) 
        end
      end     
      push!(res, (clim, invert_iso(u), [(L,R) for (_,_,L,R) in curr_v], min))
    else
      union!(queue, curr ∪ Set([lr]) for lr in LRs)
    end
  end
  res
end

"""
All given a rewrite rule, f: L ↣ R, find all pullback squares
```
           hₗ
        XL⌟→ L 
      i ↓    ↓ f
        XR → R
           hᵣ
```
Where i: XL ≤ XR in the subobject lattice of X

"""
function subobj_rule_interactions3(f::ACSetTransformation, X::ACSet)
  gr, sos = subobject_graph(X)
  esos = subobj_incl.(Ref(sos), gr[:src], gr[:tgt]) # edge monos
  _, R = dom(f), codom(f)
  res = []
  cat = WithModel(infer_acset_cat(X))
  for (iL, iR) in zip(gr[:src], gr[:tgt], esos)    
    iL == iR && continue # don't care about no-ops
    XL, XR = dom.(hom.(getindex.(Ref(sos), [iL,iR])))
    i = subobj_incl(sos, iL, iR)
    dom(i) == XL || error("Bad")
    for hᵣ in homomorphisms(XR, R; monic=false)
      hₗ, i′ = pullback(cat, f, hᵣ)
      isos = filter(isomorphisms(XL, dom(i′))) do s
       force(compose(cat, s, i′)) == force(i)
      end 
      isempty(isos) && continue
      push!(res, (iL,iR, force(compose(cat, only(isos), hₗ)), hᵣ))
    end
  end
  res
end 

# TODO # 
# Find all diagrams of the form 
#       L ←⌞XL → XG
#     f ↓    ↓   ↓
#       R ← XR → ⌜X
# With the knowledge that XR is the pullback of X and R over *something*, i.e. it 
# must be a subobject of X × R.
# If this works, we could restrict the condition that match morphisms must be 
# monic.

end # module
