# AlgebraicRewriting.jl

```@meta
CurrentModule = AlgebraicRewriting
```

Algebraic rewriting is a context-aware find-and-replace operation that is useful for maintaining structure in various scenarios. This package provides tools for such operations in Julia, ensuring that rewrite rules adhere to structures defined using ACSets (see [ACSets.jl](https://github.com/AlgebraicJulia/ACSets.jl) and [Catlab.jl](https://github.com/AlgebraicJulia/Catlab.jl)). This documentation provides a basic guide to using the AlgebraicRewriting package in Julia. 

This page will provide you with a gentle overview of how to design and apply rewrite rules for a simple ACSet. **More sophisticated examples** can be found in the side-bar.

## Setup Environment
To begin, set up your environment by importing necessary packages.

```julia
using Catlab
using AlgebraicRewriting
using DataMigrations
```

## Design a rewrite rule
The general process for designing a rewrite rule is as follows:

### 1. Define your schema 
A schema defined by a finite presentation of a generalized algebraic theory model using generators, `Ob`, `Hom`, `AttrType`, and `Attr`.

```julia
@present SchSportsTeam(FreeSchema) begin
  Player::Ob
  Team::Ob
  Member::Ob
  IsMember::Hom(Member, Player)
  MemberOf::Hom(Member, Team)

  Name::AttrType
  PlayerHasName::Attr(Player, Name)
  TeamHasName::Attr(Team, Name)
end
to_graphviz(SchSportsTeam)
```

### 2. Create the schema type 
Data for rules are stored in a data structure called an ACSet. 

```julia
@acset_type SportsTeam(SchSportsTeam)
```

### 3. Define rule parts
A rewrite rule consists of a span of ACSets (`L <-l- K -r-> R`), namely three ACSets (`L`, `K`, `R`) and two natural transformations (`l`, `r`):

- Left ACSet, `L`, is the pre-condition for the rule to be applied.
- Keep ACSet, `K`, is the data for the part of the state that remain consistent when the rule is applied.
- Right ACSet, `R`, is the effect of the rule.
- Left transformation, `l`, embeds `K` in `L`.
- Right transformation, `r`, embed `K` in `R`.

To define a rule, all five parts need to be defined. 

It is possible to insert data according to the schema using a **static** approach _or_ the **colimit-of-representables** approach.

#### Static Instantiation (`@acset`)
If using the **static** approach, you must fully specify the ACSet functors and natural transformation. Here is a rule that defines the ACSet statically. 

In this example, the rule swaps players, one from each team. `AttrVar.(1:2)`, or `[AttrVar(1), AttrVar(2)]`, are used as variable placeholders for the names of the players. This allows the rule to be applied independent of player names, as long as two players are specified from opposing teams. Contrastingly, `["Home", "Away"]`, are specified explicitly and, therefore, this rule can only be applied to teams whose names are "Home" and "Away"

```julia
# Both L and R are the same: two players are members of a Home and Away team
L = R = @acset SportsTeam{String} begin
  Player = 2; Team = 2; Member = 2; Name = 2
  IsMember = [1, 2]; MemberOf = [1, 2]
  PlayerHasName = AttrVar.(1:2)
  TeamHasName = ["Home", "Away"]
end
# K is missing the Member relation. L <- K removes the two players' memberships
# and K -> R adds in a new membership relation.
K = @acset SportsTeam{String} begin
  Player = 2; Team = 2; Name = 2
  PlayerHasName = AttrVar.(1:2)
  TeamHasName = ["Home", "Away"]
end

# Manually specify K->L and K->R
# Important that the player removed from Home (as determined by l: K->L) is 
# assigned (via r: K->R) to the player which is added to away, and vice-versa.
l = ACSetTransformation(K, L, Player=[1,2], Team=[1, 2], Name=AttrVar.([1,2]))
r = ACSetTransformation(K, R, Player=[2,1], Team=[1, 2], Name=AttrVar.([2,1])) # swap

# Alternatively we could use automated search, as there are the only two maps 
# K->L (same as K->R because L=R) that do not merge the two players together 
l, r = homomorphisms(K, L; monic=true) # ('monic' = "no merging allowed")
```

#### Colimit-of-representables instantiation (`@acset_colim`)
If using the **colimit-of-representables** approach, you only need to specify relevant objects and morphism parts. Shown here is the translation of the above rule using `@acset_colim`.

```julia
ySportsTeam = yoneda(SportsTeam{String})
L = R = @acset_colim ySportsTeam begin
  (p1, p2)::Player
  (t1, t2)::Team
  (m1, m2)::Member
  IsMember(m1) == p1
  IsMember(m2) == p2
  MemberOf(m1) == t1
  MemberOf(m2) == t2
  TeamHasName(t1) == "Home"
  TeamHasName(t2) == "Away"
end # we did not specify PlayerHasName, so it's left generic
K = @acset_colim ySportsTeam begin
  (t1, t2)::Team
  (p1, p2)::Player
  TeamHasName(t1) == "Home"
  TeamHasName(t2) == "Away"
end
l, r = homomorphisms(K, L; monic=true) # same as above because K,L,R are the same
```

### 4. Construct the rule
Use the `AlgebraicRewriting.Rule` constructor to create the rule. This assumes that a double-pushout (DPO) rewrite rule is being constructed. You may also construct an single-pushout (SPO), sesqui-pushout (SqPO), or pullback-pushout (PBPO) rule.

```julia
rule = Rule{:DPO}(l, r)
```

## Apply the rule
### 5. Define the initial state. 
Similarly, you can choose to define the acset using the static approach or the colimit-of-representable approach.

- If using the **static approach**, you must fully specify the ACSet for the initial state.

```julia
state = @acset SportsTeam{String} begin
  Player = 4; Member = 4; Team = 2
  IsMember = [1, 2, 3, 4]; MemberOf = [1, 1, 2, 2]
  TeamHasName = ["Home", "Away"]
  PlayerHasName = ["Jordan", "Alex", "Casey", "Taylor"]
end
```

- If using the **colimit-of-representable approach**, you only need to specify relevant objects and morphism parts.

```julia
state = @acset_colim ySportsTeam begin
  (p1, p2, p3, p4)::Player
  (m1, m2, m3, m4)::Member
  (t1, t2)::Team
  IsMember(m1) == p1; IsMember(m2) == p2; IsMember(m3) == p3; IsMember(m4) == p4
  MemberOf(m1) == t1; MemberOf(m2) == t1; MemberOf(m3) == t2; MemberOf(m4) == t2
  PlayerHasName(p1) == "Jordan"
  PlayerHasName(p2) == "Alex"
  PlayerHasName(p3) == "Casey"
  PlayerHasName(p4) == "Taylor"
  TeamHasName(t1) == "Home"
  TeamHasName(t2) == "Away"
end
```

### 6. Identify the match from the rule to the state
This can be done manually or automatically. 

- To **manually** identify the match, fully-specify an ACSet transformation. For this example, we would like to rule to swap `p2::Player` and `p3::Player`

```julia
pattern_match = ACSetTransformation(L, state, Player=[2, 3], Member=[2, 3], 
                                    Team=[1, 2], Name=["Alex", "Casey"])
```

- To **automatically** identify the match, use the backtracking search algorithm provided by AlgebraicRewriting. This may return multiple matches, so you can provide logic for deciding which match to select. 

```julia
pattern_match = homomorphism(L, state; initial=(Name=["Alex", "Casey"],))

matches = get_matches(rule, state)# get all four possible matches, then pick one
```

### 7. Apply the rewrite rule 
This executes the rewrite process using using the defined rule and match.

```julia
result = rewrite_match(rule, pattern_match)
```

# Authors

This documentation is maintained by [Angeline Aguinaldo](https://angelineaguinaldo.com/) and [Kristopher Brown](https://www.krisb.org/docs/research).