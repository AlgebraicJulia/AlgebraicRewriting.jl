module IHSData
export IHS

using Catlab
using Catlab.CategoricalAlgebra.CSets: ACSetColimit

const Profile = Dict{Symbol, Set{Set{Int}}}

# TODO add an IsoPattern object to store isomorphic copies of patterns. 

""" 
Data related exclusively to patterns. We store data about patterns by first decomposing them into connected components and then decompose those into subobject lattices.

Furthermore each subobject can be expressed in multiple ways as a decomposition of some other set of subobjects.
"""
@present SchIHSPattern(FreeSchema) begin 
  (Pattern, PatternCC, SubPattern, Decomp, DecompElem)::Ob
  (Int, ACSet,ACSetHom,Colim)::AttrType 
  pattern::Attr(Pattern, ACSet)
  subpattern::Hom(SubPattern, PatternCC)
  subpattern_idx::Attr(SubPattern, Int) # order in subobject_graph
  subobj::Attr(SubPattern, ACSetHom)
  pattern_cc::Attr(PatternCC, ACSet)
  pattern_coprod::Attr(Pattern, Colim)
  pattern_iso::Attr(Pattern, ACSetHom) # an isomorphism: apex(coprod) ≅ pattern

  decomp_tgt::Hom(Decomp, SubPattern)
  decomp::Hom(DecompElem, Decomp)
  decomp_src::Hom(DecompElem, SubPattern)
  decomp_colim::Attr(Decomp, Colim)
  decomp_iso::Attr(Decomp, ACSetHom)

  (Decomp2, DecompElem2)::Ob
  decomp_elem_idx::Attr(DecompElem2, Int) # order matters for colimit
  decomp_tgt2::Hom(Decomp2, SubPattern)
  decomp_colim2::Attr(Decomp2, Colim)
  decomp_iso2::Attr(Decomp2, ACSetHom)
  decomp2::Hom(DecompElem2, Decomp2)
  (decomp_elem_L, decomp_elem_R)::Hom(DecompElem2, SubPattern)
end

"""
Add information related to rules

A Rule is made up of a set of QRule (quotiented rules).
"""
@present SchIHSRule <: SchIHSPattern  begin 
  (Rule, QRule)::Ob
  Profile::AttrType
  qrule::Attr(QRule, ACSetHom)
  rule::Hom(QRule, Rule)
  profile::Attr(QRule, Profile)
  l_quot::Attr(QRule, ACSetHom)
end

"""
Interaction between patterns and rules on the basis of data for every
SubPattern × QRule pair.

This concludes all the data in an IHS that is statically computed.
"""
@present SchIHSStatic <: SchIHSRule  begin 
  (SubobjQRule, Interaction, Interaction2, Interaction3)::Ob 
  Any::AttrType
  πpat::Hom(SubobjQRule, SubPattern)
  πrule::Hom(SubobjQRule, QRule)

  patrule::Hom(Interaction, SubobjQRule)
  (iL, iR)::Attr(Interaction, ACSetHom)
  patrule2::Hom(Interaction2, SubobjQRule)
  idata::Attr(Interaction2, Any)

  (idata_L, idata_R)::Hom(Interaction3, SubPattern)
  (idata_iL, idata_iR)::Attr(Interaction3, ACSetHom)
  i_rule3::Hom(Interaction3, QRule)

end

"""
This addition to the schema adds in the runtime data. 

Each state has its own (discrete) timeline of events.

Match = CreatedMatch + InitialMatch + CreatedMatch3

Initial matches directly have a pattern. CreatedMatch has one indirectly via their Interaction. CreatedMatch3 are produced by an alternate algorithm (with 
corresponding Interaction3). 
"""
@present SchIHS <: SchIHSStatic begin 
  (State, Match, CreatedMatch, CreatedMatch3, InitialMatch,
   DecompInteraction, MatchDecomp)::Ob
  (Components)::AttrType
  # State data
  state::Attr(State, ACSet)
  curr::Attr(State, Int)
  # Data every match has 
  match_time::Attr(Match, Int)
  match_state::Hom(Match, State) # the G of Hom(X,G)
  match::Attr(Match, Components) # the data of the hom
  # Data initial matches have
  initial_match::Hom(InitialMatch, Match)
  match_pattern::Hom(InitialMatch, PatternCC)
  # Data created matches have
  created_match::Hom(CreatedMatch, Match)
  match_interaction::Hom(DecompInteraction, CreatedMatch)

  πDecomp::Hom(DecompInteraction, DecompElem)
  πInteraction::Hom(DecompInteraction,Interaction)

  # Alternate batch algorithm
  created_match3::Hom(CreatedMatch3, Match)
  matchdecomp_match::Hom(MatchDecomp, CreatedMatch3)
  matchdecomp::Hom(MatchDecomp, DecompElem2)
  matchdecomp_interaction::Hom(MatchDecomp, Interaction3)
  matchdecomp_hom::Attr(MatchDecomp, Components)

end


@acset_type IHS_(SchIHS)

const IHS = IHS_{Int,ACSet, ACSetTransformation, ACSetColimit, Profile, Any, NamedTuple}

end # module
