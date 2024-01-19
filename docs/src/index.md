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
```

## Design a rewrite rule
The general process for designing a rewrite rule is as follows:

### 1. Define your schema 
A schema defined by a finite presentation of a generalized algebraic theory model using generators, `Ob`, `Hom`, `AttrType`, and `Attr`.

```julia
@present SchTeam(FreeSchema) begin
  Player::Ob
  Team::Ob
  IsMemberOf::Hom(Player, Team)

  TeamName::AttrType
  HasName::Attr(Team, TeamName)
end
```

### 2. Create the schema type 
Data for rules are stored in a data structure called an ACSet. 

```julia
@acset_type Team(SchTeam)
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

In this example, the rule trades players, one from each team. 

```julia
L = @acset TeamStatic begin 
    Player = 4  
    Team = 2
    IsMemberOf = [1, 1, 2, 2]
    
    TeamName = ["Home", "Away"]
    HasName = [1, 2]
end
K = @acset X begin 
    TeamName = ["Home", "Away"]
end
R = @acset TeamStatic begin 
    Player = 4  
    Team = 2
    IsMemberOf = [1, 2, 1, 2]

    TeamName = ["Home", "Away"]
    HasName = [1, 2]
end
l = ACSetTransformation(K, L, TeamName=[1, 2])
r = ACSetTransformation(K, R, TeamName=[1, 2])
```

#### Colimit-of-representables instantiation (`@acset_colim`)
If using the **colimit-of-representables** approach, you only need to specify relevant objects and morphism parts. The `K` part is empty because we want all the parts specified in `L` to be rewritten. You can use `homomorphisms` to automatically define the maps `l` and `r`.

```julia
yTeam = yoneda(Team)
L = @acset_colim yTeam begin
      (p1, p2)::Player
      (team1, team2)::Team
      IsMemberOf(p1) == team1
      IsMemberOf(p2) == team2
    end
K = @acset_colim yTeam begin end
R = @acset_colim yTeam begin
      (p1, p2)::Player
      (team1, team2)::Team
      IsMemberOf(p1) == team2
      IsMemberOf(p2) == team1
    end
l = only(homomorphisms(K, L))
r = only(homomorphisms(K, R))
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
state = @acset TeamStraightforward begin 
    Player = 10  
    Team = 2
    IsMemberOf = [1, 1, 1, 1, 1, 2, 2, 2, 2, 2]
    
    TeamName = ["Home", "Away"]
    HasName = [1, 2]
end
```

- If using the **colimit-of-representable approach**, you only need to specify relevant objects and morphism parts.

```julia
state = @acset_colim yTeam begin
  (p1, p2, p3, p4, p5, p6, p7, p8, p9, p10)::Player
  (team1, team2)::Team
  IsMemberOf(p1) == team1
  IsMemberOf(p2) == team1
  IsMemberOf(p3) == team1
  IsMemberOf(p4) == team1
  IsMemberOf(p5) == team1
  IsMemberOf(p6) == team2
  IsMemberOf(p7) == team2
  IsMemberOf(p8) == team2
  IsMemberOf(p9) == team2
  IsMemberOf(p10) == team2
end
```

### 6. Identify the match from the rule to the state
This can be done manually or automatically. 

- To **manually** identify the match, fully-specify an ACSet transformation. For this example, we would like to rule to swap `p5::Player` and `p6::Player`

```julia
match = ACSetTransformation(L, state, Player=[5, 6], Team=[1, 2], TeamName=[1, 2])
```

- To **automatically** identify the match, use the backtracking search algorithm provided by AlgebraicRewriting. This may returm multiple matches, so you can provide logic for deciding which match to select. 

```julia
matches = get_matches(rule, state)
# insert logic to decide best match
```

### 7. Apply the rewrite rule 
This executes the rewrite process using using the defined rule and match.

```julia
result = rewrite_match(rule, match)
```