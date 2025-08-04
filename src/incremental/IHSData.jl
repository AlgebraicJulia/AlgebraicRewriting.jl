module IHSData
export IHS

using DataStructures: DefaultDict, OrderedDict
using JSON

using Catlab
using Catlab: ACSetColimit
using ...CategoricalAlgebra.CSets: invert_hom

const Profile = Dict{Symbol, Set{Set{Int}}}

# TODO add an IsoPattern object to store isomorphic copies of patterns. 

""" 
Data related exclusively to patterns. We store data about patterns by first decomposing them into connected components and then decompose those into subobject lattices.
"""
@present SchIHSPattern(FreeSchema) begin 
  (Pattern, PatternCC, SubPattern)::Ob # , Decomp, DecompElem)::Ob
  (Int, Bool, ACSet, ACSetHom, Colim)::AttrType 
  pattern::Attr(Pattern, ACSet)
  subpattern::Hom(SubPattern, PatternCC)
  subpattern_idx::Attr(SubPattern, Int) # order in subobject_graph
  subobj::Attr(SubPattern, ACSetHom)
  pattern_cc::Attr(PatternCC, ACSet)
  pattern_coprod::Attr(Pattern, Colim)
  pattern_iso::Attr(Pattern, ACSetHom) # an isomorphism: apex(coprod) ≅ pattern
end 

"""
Furthermore each subobject can be expressed in multiple ways as a decomposition 
of some other set of subobjects.
"""
@present SchIHSDecomp <: SchIHSPattern begin 
  (Decomp, DecompElem)::Ob
  decomp_elem_idx::Attr(DecompElem, Int) # order matters for colimit
  decomp_tgt::Hom(Decomp, SubPattern)
  decomp_colim::Attr(Decomp, Colim)
  decomp_iso::Attr(Decomp, ACSetHom)
  decomp::Hom(DecompElem, Decomp)
  (decomp_elem_L, decomp_elem_R)::Hom(DecompElem, SubPattern)
  is_minimal::Attr(Decomp, Bool)
end

"""
Add information related to rules

A Rule is made up of a set of QRule (quotiented rules).
"""
@present SchIHSRule <: SchIHSDecomp  begin 
  (Rule, QRule)::Ob
  Profile::AttrType
  rule::Hom(QRule, Rule)
  profile::Attr(QRule, Profile)
  (l_quot, r_quot, qrule)::Attr(QRule, ACSetHom)
end

"""
Interaction between patterns and rules on the basis of data for every
SubPattern × QRule pair.

This concludes all the data in an IHS that is statically computed.
"""
@present SchIHSStatic <: SchIHSRule  begin 
  Interaction::Ob
  Any::AttrType
  (idata_L, idata_R)::Hom(Interaction, SubPattern)
  (idata_iL, idata_iR)::Attr(Interaction, ACSetHom)
  i_rule::Hom(Interaction, QRule)
end

"""
This addition to the schema adds in the runtime data. 

Each state has its own (discrete) timeline of events.

Match = CreatedMatch + InitialMatch + CreatedMatch

Initial matches directly have a pattern. CreatedMatch has one indirectly via their Interaction. CreatedMatch are produced by an alternate algorithm (with 
corresponding Interaction). 
"""
@present SchIHS <: SchIHSStatic begin 
  (State, Match, CreatedMatch, InitialMatch, MatchDecomp)::Ob
  (Components)::AttrType
  # State data
  state::Attr(State, ACSet)
  curr::Attr(State, Int)
  
  # Track how state has evolved
  Update::Ob 
  update_state::Hom(Update, State)
  update_time::Attr(Update, Int)
  update_comp::Attr(Update, Components)

  # Data every match has 
  match_time::Attr(Match, Int)
  match_state::Hom(Match, State) # the G of Hom(X,G)
  match::Attr(Match, Components) # the data of the hom
  # Data initial matches have
  initial_match::Hom(InitialMatch, Match)
  match_pattern::Hom(InitialMatch, PatternCC)
  # Created Matches
  created_match::Hom(CreatedMatch, Match)
  matchdecomp_match::Hom(MatchDecomp, CreatedMatch)
  matchdecomp::Hom(MatchDecomp, DecompElem)
  matchdecomp_interaction::Hom(MatchDecomp, Interaction)
  matchdecomp_hom::Attr(MatchDecomp, Components)
end

@acset_type IHS_(SchIHS)

# Julia datatype for in memory 
const IHS = IHS_{Int, Bool, ACSet, ACSetTransformation, ACSetColimit, Profile,
                 Any, NamedTuple}

# TODO filter quotiented rule cases where you end up with "relations" which have 
# multiple parts which have the same subparts. 
"""
Generate a JSON file summarizing the static analysis of a given pattern + rule 
combination, to be consumed by external Datalog tools.
"""
function to_datalog_json(db::IHS, JSON_FILE::String; rename=Dict())
  nparts(db, :Rule) == 1 || error("Multiple rules not yet supported")
  iᶠ = findfirst(i->all(isempty,values(db[i,:profile])), parts(db, :QRule)) 
  f = db[iᶠ, :qrule] # L -> R
  nparts(db, :PatternCC) == 1 || error("Multiple patterns not yet supported")
  S = acset_schema(only(db[:pattern]))
  𝒞 = infer_acset_cat(f)
  ⋅(x,y) = compose[𝒞](x,y)
  ob_name = distinguished_object(S)

  subobjects = [cset_to_json(ϕ, ob_name; rename) for ϕ in db[:subobj]]

  X = cset_to_json(only(db[:pattern]), ob_name; rename)
  R = cset_to_json(codom(f), ob_name; rename)
  L = cset_to_json(f, ob_name; rename)


  qrules = map(parts(db, :QRule)) do qr
    qrule = db[qr, :qrule]
    r_inv = invert_hom(db[qr, :r_quot]; monic=false) # R~ -> R
    l_inv = qrule ⋅ r_inv # L~ -> R
      
    eqclasses = map(collect.(collect(db[qr, :profile][ob_name]))) do eqset 
      sort(f[ob_name].(eqset))
    end
    quintuples = []

    lr_to_ints = DefaultDict{Pair{Int,Int},Vector{Int}}(()->Int[])
    for (int, (l,r)) in enumerate(zip(db[:idata_L], db[:idata_R]))
      db[int,:i_rule] == qr && push!(lr_to_ints[l=>r], int)
    end

    for d in parts(db, :Decomp)
      XG = db[d, :decomp_tgt]
      elems = incident(db, d, :decomp)
      length(elems) == 1 || continue # only consider binary decompositions
      db[d, :is_minimal] || continue 
      elem = only(elems)
      XL = db[elem, :decomp_elem_L]
      XR = db[elem, :decomp_elem_R]
      for int in lr_to_ints[XL=>XR]
        hl = collect((db[int, :idata_iL] ⋅ l_inv)[ob_name])
        hr = collect((db[int, :idata_iR] ⋅ r_inv)[ob_name])
        push!(quintuples, (;XG,XL,XR,hl,hr))
      end
    end
    Dict(pairs((; eqclasses, quintuples)))
  end
  sort!(qrules; by=x->x[:eqclasses])

  data = ((;L, R, X, subobjects, qrules)) # Dict(pairs
  open(JSON_FILE, "w") do io 
    write(io, json(data, 2))
  end
  println(json(data, 2))
  data
end

cset_to_json(X::ACSet, var_ob::Symbol; rename) = 
  cset_to_json(id[infer_acset_cat(X)](X), var_ob; rename)

function cset_to_json(ϕ::ACSetTransformation, var_ob::Symbol; rename)
  is_monic[infer_acset_cat(ϕ)](ϕ) || error("Relabeling should be monic")
  facts = []
  X = dom(ϕ)
  S = acset_schema(X)
  vars = sort(ϕ[var_ob].(parts(X, var_ob)))
  for o in filter(!=(var_ob), ob(S))
    for p in parts(dom(ϕ), o)
      vals = map(homs(S; from=o, just_names=true)) do h 
        ϕ[var_ob](dom(ϕ)[p, h])
      end
      push!(facts, [get(rename, o, o), vals...])
    end
  end
  (; vars, facts)
end

"""
Certain schemas can be viewed as presenting relations on a set. The set is 
represented by a particular object in the schema with no outgoing morphisms.
Every other object has only outgoing morphisms and moreover all these morphisms 
go into the distinguished object. This method throws an error if the schema is 
not of this form, otherwise returns the distinguished object.
"""
function distinguished_object(S)
  dists = [o for o in ob(S) if isempty(homs(S; from=o))]
  length(dists) == 1 || error(
    "Exactly one object is allowed to have no outgoing maps: $dist")
  dist = only(dists)
  for (f, src, tgt) in homs(S)
    tgt == dist || error("All outgoing maps should be into $dist, not $f:$src→$tgt")
  end
  dist
end

end # module
