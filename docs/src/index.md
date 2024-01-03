# AlgebraicRewriting.jl

```@meta
CurrentModule = AlgebraicRewriting
```

```@autodocs
Modules = [AlgebraicRewriting.Rewrites]
Private = true
```

Algebraic rewriting is a context-aware find-and-replace operation, crucial for maintaining integrity and structure in various scenarios. This package provides tools for such operations in Julia, ensuring that replacements adhere to predefined rules or structures.

# Creating and applying rules

## Setup Environment
To begin, set up your environment by importing necessary packages.

```julia
using Catlab
using AlgebraicRewriting
```

## Design a rewrite rule
The general process for designing a rewrite rule is as follows:

1. Define your schema. This is done by defining a [finite presentation of a generalized algebraic theory model]() using generators, `Ob` and `Hom`.

```julia
@present OntTeam(FreeSchema) begin
  Player::Ob
  Team::Ob
  IsMemberOf::Hom(Player, Team)

  TeamName::AttrType
  HasName::Attr(Team, TeamName)
end
```

2. Create the schema type. Data for rules are stored in data structures called an ACSet. ACSets can be completely instantiated (straightforward way) using `StructACSet()` type constructor or dynamically instantiated (advanced way) using `DynamicACSet()` type constructor. To create the schema type, you can choose to follow the straightforward way or the advanced way.

For the **straightforward way**:
```julia
const TeamStraightforward = StructACSet("Team", OntTeam)
```

For the **advanced way**:
```julia
const TeamAdvanced = DynamicACSet("Team", OntTeam)
```

3. Define rule parts. A rewrite rule consists of a span of ACSets (`L <-l- K -r-> R`), namely three ACSets (`L`, `K`, `R`) and two natural transformations (`l`, `r`):

- Left ACSet, `L`, is the pre-condition for the rule to be applied.
- Keep ACSet, `K`, is the data for the part of the state that remain consistent when the rule is applied.
- Right ACSet, `R`, is the effect of the rule.
- Left transformation, `l`, aligns `K` to `L`.
- Right transformation, `r`, aligns `K` to `R`.

To define a rule, all five parts need to be defined. 

If using the **straightforward way**, you must fully specify the ACSet functors and natural transformation. In this example, the rule swaps player between two teams. 
```julia
L = @acset TeamStraightforward begin 
		Player = 4  
		Team = 2
		IsMemberOf = [1, 1, 2, 2]
    
    TeamName = ["Home", "Away"]
    HasName = [1, 2]
end
K = @acset X begin 
    TeamName = ["Home", "Away"]
end
R = @acset TeamStraightforward begin 
		Player = 4  
		Team = 2
		IsMemberOf = [1, 2, 1, 2]

    TeamName = ["Home", "Away"]
    HasName = [1, 2]
end
l = ACSetTransformation(K, L, TeamName=[1, 2])
r = ACSetTransformation(K, R, TeamName=[1, 2])
```

If using the **advanced way**, you only need to specify relevant objects and morphism parts. The `K` part is empty because all the parts specified in `L` and `R` change. (Note: `SchRule` is from `AlgebraicRewriting`)
```julia
diagram = @migration(SchRule, OntTeam,
  begin
    L => @join begin
      (p1, p2)::Player
      (team1, team2)::Team
      IsMemberOf(p1) == team1
      IsMemberOf(p2) == team2
    end
    K => @join begin end
    R => @join begin 
      (p1, p2)::Player
      (team1, team2)::Team
      IsMemberOf(p1) == team2
      IsMemberOf(p2) == team1
    end
  end)
```

4. Construct the rule. Use the `AlgebraicRewriting.Rule` constructor to create the rule. This assumes that a double-pushout (DPO) rewrite rule is being constructed. You may also construct an single-pushout (SPO), sesqui-pushout (SqPO), or pullback-pushout (PBPO) rule.

If using the **straightforward way**, package the rule in terms of maps, l and r, using the `AlgebraicRewriting.Rule` constructor directly. 
```julia
rule = Rule{:DPO}(l, r)
```

If using the **advanced way**, you have to (1) compute the colimit of representables in order to obtain the fully-specified ACSets for L, K, and R; (2) infer the maps l and r, and (3) package the rule using the AlgebraicRewriting.Rule constructor.

```julia
yTeam = yoneda(TeamAdvanced)
rule = colimit_representables(diagram, yTeam)
l = rule_hom_map(rule, :l, rule_ob_map(rule, Symbol(K), rule_ob_map(rule, Symbol(L))
r = rule_hom_map(rule, :r, rule_ob_map(rule, Symbol(K), rule_ob_map(rule, Symbol(R))
rule = Rule{:DPO}(l, r)
```

## Apply the rule
1. Define the initial state. 

If using the **straightforward way**, you must fully specify the ACSet for the initial state.
```
state = @acset TeamStraightforward begin 
		Player = 10  
		Team = 2
		IsMemberOf = [1, 1, 1, 1, 1, 2, 2, 2, 2, 2]
    
    TeamName = ["Home", "Away"]
    HasName = [1, 2]
end
```

If using the **advanced way**, you only need to specify relevant objects and morphism parts.
```
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


2. Identify the match from the rule to the state. This can be done manually or automatically. 

To **manually** identify the match, fully-specify an ACSet transformation. For this example, we would like to rule to swap `p5::Player` and `p6::Player`
```julia
match = ACSetTransformation(L, state, Player=[5, 6], Team=[1, 2], TeamName=[1, 2])
```

To **automatically** identify the match, use the backtracking search algorithm provided by AlgebraicRewriting. This may returm multiple matches, so you can provide logic for deciding which match to select. 
```julia
matches = get_matches(rule, state)
# insert logic to decide best match
```

3. Apply the rewrite rule. This executes the rewrite process using using the defined rule and match.

```
result = rewrite_match(rule, match)
```

This documentation provides a basic guide to using the AlgebraicRewriting package in Julia. 

# Examples

You may visit these pages to view more elaborate applications of AlgebraicRewriting.jl:

- [full demo](https://github.com/AlgebraicJulia/AlgebraicRewriting.jl/blob/main/docs/src/full_demo.jl): a small demonstration of most of the major features 
  of AlgebraicRewriting.
- [Lotka Volterra example](https://github.com/AlgebraicJulia/AlgebraicRewriting.jl/blob/main/docs/src/lotka_volterra.jl): a model based 
  on NetLogo's [wolf-sheep predation](http://ccl.northwestern.edu/netlogo/models/WolfSheepPredation) agent-based model demo.
- [Game of Life example](https://github.com/AlgebraicJulia/AlgebraicRewriting.jl/blob/main/docs/src/GameOfLife.ipynb): an implementation of Conway's 
  [game of life](https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life) on an 
  arbitrary graph (with the grid-structure as a special case).