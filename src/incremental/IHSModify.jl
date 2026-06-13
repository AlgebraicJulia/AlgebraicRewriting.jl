module IHSModify

using DataStructures
using Catlab
using Combinatorics: partitions

using ...CategoricalAlgebra.CSets: invert_iso
using ..Algorithms: connected_acset_components, all_epis
import ..IHSData: IHS
using ..IHSAccess: pattern_cc, empty_profile, qrules, subobj_incl, subobj_eq, subobj_lt


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
  # Check if result is cached already
  found = findfirst(==(pattern_cc), ihs[:pattern_cc])
  isnothing(found) || return found

  # Declare a new pattern which is assumed to be fully connected
  subobjs = subobject_graph(pattern_cc) 
  iₚ = add_part!(ihs, :PatternCC; pattern_cc, subobj_graph=subobjs)
  subobjects = enumerate(force.(hom.(subobjs[2])));
  # Register each subobject of the connected component
  subobj_ids = map(subobjects) do (subpattern_idx, subobj)
    add_part!(ihs, :SubPattern; subpattern=iₚ, subobj, subpattern_idx)    
  end

  # Look for interactions between (quotiented) rules and the (CC) pattern
  for i_rule in qrules(ihs)
    f = ihs[i_rule, :q]
    for (idata_iL, idata_iR, L, R) in subobj_rule_interactions4(f, subobjs)
      idata_L, idata_R = subobj_ids[[L,R]]
      add_part!(ihs, :Interaction; idata_iL, idata_iR, idata_L, idata_R, i_rule=iᵣ)
    end
  end

  # Register all ways to decompose the (CC) pattern
  decomposition_sets = alt_decomps2(pattern_cc) # a set of decompositions per subobj of pattern
  for (iₛ, decomp_colim, decomp_iso,  d) in decomposition_sets
    # iₛ is the index into the subobjects of `pattern_cc`. 
    decomp_tgt = subobj_ids[iₛ] # The 'old' subobject of the decomposition
    # Add a row for the decomposition
    decomp = add_part!(ihs, :Decomp; decomp_tgt, decomp_colim, decomp_iso)
    for (decomp_elem_idx, (L_id,R_id)) in enumerate(d)
      # Register each new contribution to the decomposition
      decomp_elem_L, decomp_elem_R = subobj_ids[[L_id,R_id]]
      add_part!(ihs, :DecompElem; decomp, decomp_elem_L, decomp_elem_R, decomp_elem_idx)
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
  epis, _ = all_epis(dom(rule))
  for l_quot in epis
    r_quot, qrule = force.(legs(pushout[cat](rule, l_quot)))
    profile = merge_profile(l_quot)
    q = add_part!(ihs, :QRule; profile, l_quot, r_quot, qrule, rule=iᵣ)
    
    for p_cc in parts(ihs, :PatternCC)
      so_ids = incident(ihs, p_cc, :subpattern)
      subobjs = ihs[p_cc, :subobj_graph]
      for (L, R, idata_iL, idata_iR) in subobj_rule_interactions4(qrule, subobjs)
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

""" Pick out a (full) subgraph via its vertices """
function subgraph(g::AbstractGraph, vertices::AbstractVector)
  hom(Subobject(g; V=vertices, E=collect(filter(edges(g)) do e 
    all(∈(vertices), [src(g, e), tgt(g, e)]) 
  end)))
end

""" 
Subobject picked out by starting with some part and following its 
outhoms 
"""
function representable_elem_subobj(X::ACSet, oₒ::Symbol, iₒ::Int)
  S = acset_schema(X)
  pts = Dict(o=>Int[] for o in ob(S))
  push!(pts[oₒ], iₒ)
  queue = [oₒ => iₒ]
  while !isempty(queue)
    o, i = pop!(queue)
    for (f, _, c) in homs(S; from=o)
      if X[i, f] ∉ pts[c]
        push!(pts[c], X[i, f])
        push!(queue, c => X[i, f])
      end
    end
  end
  Subobject(X; pts...)
end

"""
Alternative approach to finding multidecompositions. Let P ⊂ Sub Q be the 
subposet of join-irreducibles (these are a quotient of representables) and let 
J(x) ⊆ P be the representation of x ∈ Sub Q as a join of these join-irreducibles.
A multidecomposition is identified with a choice QG ∈ Sub Q and a partition 
of the connected components of P∖J(QG). Each such partition can be joined to 
yield one of the components of the multidecomposition as a subobject of Q.
"""
function alt_decomps2(X::ACSet; check=true)
  S = acset_schema(X)
  gr, sos = subobject_graph(X);
  cat = infer_acset_cat(X)
  𝒞 = WithModel(cat)

  hsos = force.(hom.(sos)) # subobjects as morphisms
  dsos = dom.(hsos)        # shapes of the subobjects
  emp = sos[end]           # empty subobject
  cat = infer_acset_cat(X)
  N = length(sos)
  # join irreducibles are representables
  jir = Int[]
  for o in ob(S)
    for i in parts(X, o)
      so = representable_elem_subobj(X, o, i)
      push!(jir, findfirst(so′-> subobj_eq(so, so′), sos))
    end
  end
  # Express each subobject as a join of join-irreducibles
  ji_decomps = [inneighbors(gr, i) ∩ jir for i in 1:N]
  decomps = Tuple[]
  for iG in 2:N
    QG = sos[iG]
    jiGr = subgraph(gr, setdiff(jir, ji_decomps[iG]))
    ccs = connected_components(dom(jiGr))
    for partis in partitions(1:length(ccs))
      comps = sort(map(partis) do part
        A = @withmodel cat (∨) begin 
          foldl(∨, sos[jiGr[:V].(vcat(ccs[part]...))]; init=emp)
        end
        findfirst(so′-> subobj_eq(A, so′), sos)
      end) # canonical order
      check && check_multidecomp(sos, iG, Set(comps)) || error("Bad decomp")

      intersections = @withmodel cat (∧) begin 
        [findfirst(so′-> subobj_eq(A ∧ QG, so′), sos) for A in sos[comps]]
      end
      LRs = collect(zip(intersections, comps))
      ob1 = dsos[intersections]
      ob2 = dsos[[iG; comps]]

      homs = vcat(map(enumerate(LRs)) do (i, (L,R))
        [(subobj_incl(sos, L, iG), i, 1), (subobj_incl(sos, L, R), i, i+1)] 
      end...)

      bpd = BipartiteFreeDiagram(ob1, ob2, homs)

      clim = colimit(𝒞, bpd)
      csp = Multicospan(hsos[[iG; comps]])
      u = universal(𝒞, clim, csp) |> force
      is_monic(u) || error("PUSHOUT MUST  BE SUBOBJECT")
      out = findfirst(hom.(sos)) do so 
        any(isomorphisms(dom(u), dom(so))) do σ
          force(compose(𝒞, σ, so)) == u
        end
      end
      out == 1 || error("PUSHOUT MUST BE TOP SUBOBJECT")
      push!(decomps, (iG, clim, invert_iso(u), LRs))
    end
  end
  decomps
end

""" Confirm that a purported multidecomposition satisfies the definition """
function check_multidecomp(subobjs, iQG, iQRs::AbstractSet)::Bool
  QG = subobjs[iQG]
  QRs = [subobjs[i] for i in iQRs] # enforce an order
  X = codom(hom(QG))
  emp = Subobject(X)
  cat = infer_acset_cat(X)

  # 1: the union of all must be ⊤
  @withmodel cat (∨) begin 
    @assert is_isomorphic(X, dom(hom(QG ∨ foldl(∨, QRs; init=emp))))
  end
  # 2: Non-redundancy: QRᵢ ≰ QG
  for QR in QRs 
    @assert !subobj_lt(QR, QG)
  end
  # 3: Overlap containment: QRᵢ∧QRⱼ≤QG
  for (i, QR) in enumerate(QRs), QR′ in QRs[i+1:end]
    @withmodel cat (∧) begin 
      @assert subobj_lt(QR ∧ QR′, QG)
    end
  end
  # 4: Non-redundancy 
  for QR in QRs
    @withmodel cat (∨,~) begin
      QR′ = foldl(∨, filter(!=(QR),QRs); init=emp)
      @assert subobj_eq(QR, ~(QG ∨ QR′))
    end
  end
  true 
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
function subobj_rule_interactions3(f::ACSetTransformation, subobjs)
  gr, sos = subobjs
  esos = subobj_incl.(Ref(sos), gr[:src], gr[:tgt]) # edge monos
  _, R = dom(f), codom(f)
  res = []
  cat = WithModel(infer_acset_cat(R))
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

function subobj_rule_interactions4(f::ACSetTransformation, subobjs; check=false)
  gr, sos = subobjs
  L, R,S  = dom(f), codom(f), acset_schema(f)
  𝒞 = infer_acset_cat(L)
  imgs = [Dict(o=>Set(collect(so.hom[o])) for o in ob(S)) for so in sos]
  untouched = Dict(o=>setdiff(parts(R,o),collect(f[o])) for o in ob(S))
  res = []
  hom_cache = Dict{ACSet, Vector{ACSetTransformation}}()

  for iR in 1:length(sos)
    QR = dom(sos[iR].hom)
    for iL in filter(!=(iR), gr[incident(gr,iR,:tgt),:src])
      QL = dom(hom(sos[iL]))

      # ι = ιs[iL => iR]
      ut = Dict(o=>findall(i->sos[iR].hom[o](i) ∉ imgs[iL][o], parts(QR,o)) for o in ob(S))
      hs =  if haskey(hom_cache, QL)
        hom_cache[QL]
      else 
        hom_cache[QL] = homomorphisms(QL, L; monic=false)
      end

      for hₗ in hs
        # try to extend to a pullback
        @withmodel 𝒞 (⋅) begin 
          # Step 1: make sure hᵣ forms commutative square
          initial = Dict{Symbol, Dict{Int,Int}}(map(ob(S)) do o 
            o => Dict{Int,Int}(map(parts(QL,o)) do i
              i′=sos[iL].hom[o](i)
              findfirst(r-> sos[iR].hom[o](r)==i′, parts(QR, o)) => f[o](hₗ[o](i))
            end)
          end)
          # Step 2: make sure pb property holds
          predicates = Dict(o => Dict(i=>untouched[o] for i in ut[o]) for o in ob(S))

          for hᵣ in homomorphisms(QR, R; initial, predicates)
            push!(res, (iL,iR, hₗ, hᵣ))
          end
        end
      end
    end
  end
  if check 
    expected = subobj_rule_interactions3(f, subobjs)
    for r in res 
      r ∈ expected || error("Extra $r ")
    end
    for e in expected 
      e ∈ res || error("Missing $e")
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
