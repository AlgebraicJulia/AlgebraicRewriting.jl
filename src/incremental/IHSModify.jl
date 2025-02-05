module IHSModify

export cokernel 

using DataStructures
using Catlab
using Catlab.CategoricalAlgebra.CSets: SubACSetComponentwise
using Catlab.CategoricalAlgebra.Chase: collage, extend_morphism_constraints

using ...CategoricalAlgebra.CSets: invert_iso,pushout_complement, can_pushout_complement
using ..Algorithms: connected_acset_components, all_epis, all_subobjects
import ..IHSData: IHS, Profile
using ..IHSAccess: pattern_ccs, pattern_cc, curr, empty_profile, qrules, 
                   subobj_lt, subobj_incl


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
    iₛ = add_part!(ihs, :SubPattern; subpattern=iₚ, subobj, subpattern_idx)
    add_patrule!.(Ref(ihs), iₛ, qrules(ihs))
    iₛ
  end

  for i_rule3 in qrules(ihs)
    f = ihs[i_rule3, :q]
    for (idata_iL, idata_iR, L, R) in subobj_rule_interactions3(f, pattern_cc)
      idata_L, idata_R = so_ids[[L,R]]
      add_part!(ihs, :Interaction3; idata_iL, idata_iR, idata_L, idata_R, i_rule3=iᵣ)
    end
  end

  dcs = alt_decomps(pattern_cc)
  for (iₛ, dc) in enumerate(dcs)
    for (decomp_colim2, decomp_iso2,  d) in dc 
      decomp2 = add_part!(ihs, :Decomp2; decomp_tgt2 = so_ids[iₛ],
                          decomp_colim2, decomp_iso2)
      for (decomp_elem_idx, (v1,v2)) in enumerate(sort(d))
        decomp_elem_L, decomp_elem_R = so_ids[v1], so_ids[v2] 
        add_part!(ihs, :DecompElem2; decomp2, decomp_elem_L, decomp_elem_R, 
                  decomp_elem_idx)
      end
    end
  end


  for (k,vss) in pairs(decomps(sos))
    for vs in vss 
      decomp_colim, decomp_iso = complement_isos(sos[k], sos[vs])
      decomp = add_part!(ihs, :Decomp; decomp_tgt=so_ids[k],
                         decomp_colim, decomp_iso)
      for v in vs 
        add_part!(ihs, :DecompElem; decomp, decomp_src=so_ids[v])
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

  iᵣ = add_part!(ihs, :Rule)
  for qL in reverse(all_epis(dom(rule)))
    _, qf = pushout(rule, qL)
    profile = merge_profile(qL)
    q = add_part!(ihs, :QRule; profile, l_quot=qL, qrule=qf, rule=iᵣ)
    add_patrule!.(Ref(ihs), parts(ihs, :SubPattern), Ref(q))
    
    for p_cc in parts(ihs, :PatternCC)
      so_ids = incident(ihs, p_cc, :subpattern)
      X = ihs[p_cc, :pattern_cc]
      for (L, R, idata_iL, idata_iR) in subobj_rule_interactions3(qf, X)
        idata_L, idata_R = so_ids[[L,R]]
        add_part!(ihs, :Interaction3; idata_iL, idata_iR, idata_L, idata_R, i_rule3=q)
      end
    end
  end
  iᵣ
end


"""
Do precomputation for a given a (sub)pattern + rule pair
"""
function add_patrule!(ihs::IHS, iₚ::Int, iᵣ::Int)
  sol = incident(ihs, iₚ, :πpat) ∩ incident(ihs, iᵣ, :πrule) 
  isempty(sol) || error("Patrule already present")
  patrule = add_part!(ihs, :SubobjQRule; πpat=iₚ, πrule=iᵣ)
  A, f = ihs[iₚ, :subobj], ihs[iᵣ, :qrule]

  for (iL, iR) in subobj_rule_interactions(f, A)
    add_part!(ihs, :Interaction; iL, iR, patrule)
  end
  for idata in subobj_rule_interactions2(f, A)
    add_part!(ihs, :Interaction2; idata, patrule2=patrule)
  end


  patrule
end

"""
Start tracking a new state with respect to all rule+pattern pairs.
"""
function add_state!(ihs::IHS, state::ACSet)
  iₛ = add_part!(ihs, :State; state, curr=0)
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
function merge_profile(f::ACSetTransformation)::Profile
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

""" Get unordered pairs, not including two copies of same element """
function non_id_pairs(v::AbstractVector) 
  N = length(v)
  vcat(map(1:N-1) do i 
    map(i+1:N) do j 
      (v[i], v[j])
    end 
  end...)
end

""" Merge together non-new material of a rule L ↣ R via pushout with L → 1 """
cokernel(f::ACSetTransformation) = pushout(f, delete(dom(f)))



# Decomposing with subobjects
#############################
""" 
Turn A ↣ X into X as a pushout of A and ~A plus an iso from the apex to X
"""
function subobj_decompose(A::ACSetTransformation)
  nA = hom(~(Subobject(A)))
  pb = pullback(A, nA)
  po = pushout(pb...)
  u = universal(po, Cospan(A, nA))
  (po, invert_iso(u))
end

# Decompose a subobject (regarded as a task) into subtasks
#---------------------------------------------------------
decomps(sos::Vector) = Dict(k=>decomps(sos, k) for k in 1:length(sos))

"""
We look at subobjects as requests for certain things to be filled in.

E.g.[- • • •] ↣ [•→•→•→•] is a request "add v1, e1, e2, and e3".

We want to decompose such a request into a set of smaller requests, e.g.

[• •→•→•] (adds v1,e1) [•→• •→•] (adds e2) [•→•→• •] (adds e3)

One way to make this precise is to say we want a set of subobjects A↣Bᵢ↣X

such that ∨ᵢ ~Bᵢ ∨ A  = X (the missing elements of Bᵢ complete A to X)
and that  Bᵢ ≤ A ∨ V(j≠i) Bⱼ.
"""
function decomps(sos::Vector, Base::Int)
  A = sos[Base]
  Aꜛs = filter(i-> i!= Base && subobj_lt(A, sos[i]), 2:length(sos))
  comps = Dict(i => ~sos[i] for i in Aꜛs)
  res, seen = Set(), Set()
  good_meetsᵢ = Dict(map(Aꜛs) do i 
    i => Set(filter(Aꜛs) do j
      subobj_lt(hom(~sos[i] ∧ ~sos[j]), hom(A))
    end)
  end)

  queue = [Set([i]) => good_meetsᵢ[i] for i in Aꜛs]

  while !isempty(queue)
    curr, good_meets = pop!(queue)
    curr ∈ seen && continue 
    push!(seen, curr)
    join = hom(foldl(∨, [comps[i] for i in curr]; init=A))
    if is_epic(join) 
      no_magic = all(curr) do i 
        no_i = hom(foldl(∨, [comps[j] for j in curr if j!=i]; init=A))
        subobj_lt(hom(sos[i]), no_i )
      end
      no_magic && push!(res, curr)
    else 
      for Aꜛ in good_meets
        if subobj_lt(join, hom(sos[Aꜛ]))
          new_set = Set([Aꜛ; curr...])
          new_meets = good_meets ∩ good_meetsᵢ[Aꜛ]
          push!(queue, new_set=>new_meets)
        end
      end
    end
  end
  [[Base], sort([sort(collect(r)) for r in res]; by=length)...]
end

""" 
Indices in iBs refers to sos, not Aꜛs. This function exists just for debugging.
"""
function is_good_decomp(sos, Base, iBs)::Bool
  A = sos[Base]
  for i in iBs, j in iBs 
    i == j && continue
    subobj_lt(hom(~sos[i] ∧ ~sos[j]), hom(A)) || return false
  end
  full_join = hom(foldl(∨, [~sos[i] for i in iBs]; init=A))
  is_epic(full_join) || return false
  all(iBs) do i 
    no_i = hom(foldl(∨, [~sos[j] for j in iBs if j!=i]; init=A))
    subobj_lt(hom(sos[i]), no_i )
  end
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
  res = Set{Tuple{Any,Any,Vector{Tuple{Int,Int}}}}()
  hsos = force.(hom.(sos))
  dsos = dom.(hsos)
  A =  hsos[iₐ] # subobject representing "old data"

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
  
    clim = colimit(bpd)
    csp = Multicospan([A, getindex.(Ref(hsos), last.(curr_v))...])
    u = universal(clim, csp) |> force
    is_monic(u) || continue # check if pushout is even a subobject
    out = findfirst(hom.(sos)) do so 
      any(isomorphisms(dom(u), dom(so))) do σ
        force(σ ⋅ so) == u
      end
    end
    if out == 1
      push!(res, (clim, invert_iso(u), [(L,R) for (_,_,L,R) in curr_v]))
    else
      union!(queue, curr ∪ Set([lr]) for lr in LRs)
    end
  end
  res
end

# Express a decomposition as a bipartite diagram
#-----------------------------------------------
"""
Given a set of subobjects, Aᵢ ↣ X, we can construct a Bipartite diagram with 
an ob₁ of Aᵢ ∧ Aⱼ for every unordered pair (i,j) and projection maps into ob₂
which is just Aᵢ. If one takes the colimit of this diagram, one gets the union
of all the As.
"""
function intersection_bpd(As::Vector{<:ACSetTransformation})
  N = length(As)
  N > 1 || error("Must be nonempty")
  ps = non_id_pairs(1:N)
  allequal(codom.(As)) || error("$As should be a cospan")
  ∂Xᵢ = [pullback(As[i], As[j]) for (i,j) in ps]

  homs = vcat(map(enumerate(zip(ps, ∂Xᵢ))) do (idx, ((i,j), AiAj))
    l1,l2 = legs(AiAj)
    [(l1, idx, i), (l2, idx, j)] 
  end...)
  
  BipartiteFreeDiagram(apex.(∂Xᵢ), dom.(As), homs)
end

function span_pushout(s::Multispan)
  hs = [(h, 1, i) for (i,h) in enumerate(s)]
  bpd = BipartiteFreeDiagram([apex(s)], codom.(s), hs)
  colimit(bpd)
end

"""
Glue together a root subobject, A ↣ X, with the complements of its 
decomposition, Bᵢ, i.e. X ≅ A ∨ ~Bᵢ
"""
function complement_isos(root::Subobject, combo::Vector{<:Subobject})
  root = hom(root)
  bpd = intersection_bpd([root, [hom(~k) for k in combo]...])
  clim = colimit(bpd)
  u = universal(clim, Multicospan([root, [hom(~k) for k in combo]...]))
  (clim, invert_iso(u))
end

"""
We look for maps m: ~A → ~L such that pb(f, m) yields ∂A↣~A.
 
```
               f
            R  ↢ L                 
       m⋅cL ↑    ↑   
           ~A ↢⌜∂A 
           
```
The the fact the new material (what's left to bring A to X) must all come from 
R, in particular the the part of R that is not in L. The pullback condition 
guarantees that the only part of this map that IS in L is just the boundary.
"""
function subobj_rule_interactions(f::ACSetTransformation,
  A::ACSetTransformation)
  cA, cL = [force(hom(~Subobject(x))) for x in [A,f]]
  ∂_cA = force(subobj_incl(hom(Subobject(A) ∧ Subobject(cA)), cA))
  res = []
  for m in homomorphisms(dom(cA), dom(cL))
    ∂_cA′, to_L =  pullback(m⋅cL, f)
    codom(to_L) == dom(f) || error("Bad")
    σs = filter(isomorphisms(dom(∂_cA), dom(∂_cA′))) do σ
      force(σ ⋅ ∂_cA′) == ∂_cA
    end
    isempty(σs) && continue
    push!(res, (force(only(σs) ⋅ to_L), force(m⋅cL))) # (∂A→L, ~A→R)
  end
  res
end


"""
All partial maps A ↢ • → L such that the pushout complements 
with 
"""
function subobj_rule_interactions2(f::ACSetTransformation,
  A::ACSetTransformation)
  L, R = dom(f), codom(f)
  res = []
  for ∂A in hom.(subobject_graph(dom(A))[2])
    dom(∂A) == Graph(6) && println("HERE")
    can_pushout_complement(∂A, A) || continue 
    to_A′, A′ = pushout_complement(∂A, A)
    is_epic(to_A′) && continue # this would recover old homs
    # isempty(codom(to_A′)) && continue # makes more sense??? but wrong???

    # Express X as a pushout of A and A′
    po = pushout(∂A, to_A′)
    σ = invert_iso(universal(po, Cospan(A,A′)))

    for hᵣ in homomorphisms(codom(to_A′), R)
       hₗ, to_A′′ = pullback(f, hᵣ)
       isos = filter(isomorphisms(dom(to_A′), dom(to_A′′))) do s
        force(s ⋅ to_A′′) == force(to_A′)
       end 
       isempty(isos) && continue
      push!(res, (∂A, only(isos) ⋅ hₗ, hᵣ, po, σ))
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
  for (iL, iR) in zip(gr[:src], gr[:tgt], esos)    
    iL == iR && continue # don't care about no-ops
    XL, XR = dom.(hom.(getindex.(Ref(sos), [iL,iR])))
    i = subobj_incl(sos, iL, iR)
    dom(i) == XL || error("Bad")
    for hᵣ in homomorphisms(XR, R; monic=false)
      hₗ, i′ = pullback(f, hᵣ)
      isos = filter(isomorphisms(XL, dom(i′))) do s
       force(s ⋅ i′) == force(i)
      end 
      isempty(isos) && continue
      push!(res, (iL,iR, only(isos) ⋅ hₗ, hᵣ))
    end
  end
  res
end 

"""
EXPERIMENTAL, NOT WORKING YET

Find all diagrams of the form 

      L ←⌞XL → XG
    f ↓    ↓   ↓
      R ← XR → ⌜X

With the knowledge that XR is the pullback of X and R over *something*, i.e. it 
must be a subobject of X × R.

If this works, we could restrict the condition that match morphisms must be 
monic.
"""
function subobj_rule_interactions_nonmonic(f::ACSetTransformation,
  XG::ACSetTransformation)
  R = codom(f)
  X = codom(XG)
  res = []
  πX,πR = prod = product(X, R)
  for eqXR in all_subobjects(ob(prod))
    XR = eqXR ⋅ πX # map from XR → X 
    to_R = eqXR ⋅ πR
    ∂_XR, to_L = pb = pullback(to_R, f)
    for ∂_XG in homomorphisms(apex(pb), dom(XG))
      force(∂_XR⋅XR) == force(∂_XG ⋅ XG) || continue
      fromXG, fromXR = po = pushout(∂_XG, ∂_XR)
      dom(fromXR) == dom(XR) || error("Bad")
      for σ in isomorphisms(apex(po), X) 
        force( XG ) == force(fromXG⋅ σ) || continue
        force( XR) == force(fromXR⋅ σ) || continue
        push!(res, (to_R, to_L, po, σ))
      end
    end
  end
  res 
end



end # module
