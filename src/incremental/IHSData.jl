module IHSData
export IHS

using Catlab
using Catlab.CategoricalAlgebra.CSets: ACSetColimit

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
Furthermore each subobject can be expressed in multiple ways as a decomposition of some other set of subobjects.
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

end # module
