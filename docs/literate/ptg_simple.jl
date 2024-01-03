using Pkg
cd("/Users/aguinam1/Documents/Git/aaguinal.github.io/assets/slides/aaai-symposiumtalk-2023/julia")  # use this environment to avoid `constructor` error
Pkg.activate(".")
Pkg.instantiate()
using PrettyTables

using Catlab
using AlgebraicRewriting

############################### SCHEMA ###############################
# Create an ontology by defining a finite presentation of a freely generated category using @present macro

# About the world: The Bread World Ontology has the types Thing, BreadLoaf, Countertop, and Stool. The Breadloaf, Countertop, and Stool types have morphisms to Thing that represent is-a relationships. The InOn type can be used to encode a set relation (as opposed to a function) that was two morphisms going to Thing. One morphism points out the LHS of the relation and the other morphism point out the RHS of the relation.

@present OntBreadWorld(FreeSchema) begin
  Thing::Ob
  BreadLoaf::Ob
  Countertop::Ob
  Stool::Ob

  BreadLoafIsThing::Hom(BreadLoaf, Thing)  # is-a
  CountertopIsThing::Hom(Countertop, Thing)  # is-a
  StoolIsThing::Hom(Stool, Thing)  # is-a

  InOn::Ob
  inOn_l::Hom(InOn, Thing)
  inOn_r::Hom(InOn, Thing)
end

# Visualize the ontology
to_graphviz(OntBreadWorld)

# Make the ontology an acset type
@acset_type BreadWorld(OntBreadWorld)

############################### RULE ###############################
# Construct rule by defining a span in the category of ACSets

# Use the @acset macro to define an ACSet functor. The LHS refers to a type (or object) in our ontology and the RHS defines the set assignment using FinFunctions. For this, you need to completely specify the ACSet functor, i.e. every object and morphism in the index category must be specified. 

# About the rule: This rule moves a breadloaf from a countertop to a stool.

# Left ACSet
L = @acset BreadWorld begin
  Thing = 3
  BreadLoaf = 1
  Countertop = 1
  Stool = 1

  BreadLoafIsThing = [1]
  CountertopIsThing = [2]
  StoolIsThing = [3]

  InOn = 1
  inOn_l = [1]
  inOn_r = [2]  # breadloaf is on the countertop
end

# Middle/Keep ACSet
# The Thing, Breadloaf, Countertop, and Stool types should be held constant. The InOn type will change because we are changing the underlying set function.
K = @acset BreadWorld begin
  Thing = 3
  BreadLoaf = 1
  Countertop = 1
  Stool = 1
end

# Right ACSet
R = @acset BreadWorld begin
  Thing = 3
  BreadLoaf = 1
  Countertop = 1
  Stool = 1

  BreadLoafIsThing = [1]
  CountertopIsThing = [2]
  StoolIsThing = [3]

  InOn = 1
  inOn_l = [1]
  inOn_r = [3]  # breadloaf is on the stool
end

# Left leg of span
l = ACSetTransformation(K, L, Thing=[1, 2, 3], BreadLoaf=[1], Countertop=[1], Stool=[1])

# Right leg of span
r = ACSetTransformation(K, R, Thing=[1, 2, 3], BreadLoaf=[1], Countertop=[1], Stool=[1])

# Use AlgebraicRewriting.Rule wrapper to add a rule interface
moveBreadRule = Rule(l, r)

############################### WORLD STATE ###############################
# Define a world state using the @acset macro. This is the ACSet way of specifying an ACSet. For this, you need to completely specify the ACSet functor, i.e. every object and morphism in the index category must be specified. The ACSets must be specified in terms of FinFunctions.

# About the world state: In this world state, there are two countertops, one stool, and one breadloaf. All of these amount to four things. The breadloaf is on the first countertop. 

state = @acset BreadWorld begin
  Thing = 4
  BreadLoaf = 1
  Countertop = 2
  Stool = 1

  BreadLoafIsThing = [1]
  CountertopIsThing = [2, 3] # there are two countertops
  StoolIsThing = [4]

  InOn = 1
  inOn_l = [1]  # breadloaf is on the countertop 1
  inOn_r = [2]
end

############################### APPLY RULE ###############################
# Use the AlgebraicRewriting.get_matches(::Rule{T}, ::ACSet) utility function to find matches between the rule and the state.
matches = get_matches(moveBreadRule, state)

# Take the first match
match = matches[1]

# Compute the new world state after rewriting
new_state = rewrite_match(moveBreadRule, match)