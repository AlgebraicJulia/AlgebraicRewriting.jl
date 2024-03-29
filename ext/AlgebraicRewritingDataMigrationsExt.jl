module AlgebraicRewritingDataMigrationsExt 

using Catlab
using ACSets.DenseACSets: constructor
using DataMigrations

using AlgebraicRewriting
import AlgebraicRewriting.Rewrite: Rule, PBPORule 


# Alternate constructors for rules 
##################################

""" Create a rewrite rule from a span-shaped conjunctive data migration.

For convenience, the rule may be partially specified. If the feet or apex are
omitted, they are taken to be empty. Any leg that is omitted will be inferred
automatically; an error will be raised if the required homomorphism does not
exist or is not unique.

Positive/negative application conditions are stored in the result but not as 
genuine application conditions because we want to be able to apply the rule 
even when the conditions don't hold. (We track them to be able to report user 
errors.)
"""
function Rule(rule_schema::DataMigration, y; semantics=:DPO, kw...)
  rule = colimit_representables(rule_schema, y)
  L, R, K = [rule_ob_map(rule, Symbol(x)) for x in "LRK"]
  l = rule_hom_map(rule, :l, K, L)
  r = rule_hom_map(rule, :r, K, R)
  Rule{semantics}(l, r; kw...)
end

function PBPORule(rule_schema::FinDomFunctor, y; kw...)
  rule = colimit_representables(rule_schema, y)
  L, R, K, L′, K′ = [rule_ob_map(rule, x) for x in [:L,:R,:K,:L′,:K′]]
  l = rule_hom_map(rule, :l, K, L)
  r = rule_hom_map(rule, :r, K, R)
  tl = rule_hom_map(rule, :tₗ, L, L′)
  tk = rule_hom_map(rule, :tₖ, K, K′)
  l_ = rule_hom_map(rule, :l′, K′, L′)
  PBPORule(l, r, tl, tk, l_; kw...)
end

# Help parse the @migration diagram 
###################################
function rule_ob_map(rule, name::Symbol)
  try
    ob_map(rule, name)
  catch
    constructor(first(collect_ob(rule)))() # Default to empty database.
  end
end

function rule_hom_map(rule, name::Symbol, dom, codom)
  try
    hom_map(rule, name)
  catch
    return only(homomorphisms(dom, codom))
  end
end

function rule_inputs(rule_schema)
  I = ob_map(rule_schema, :I)
  (ob_map(I, j) for (_, j) in named_ob_generators(shape(I)))
end

function rule_outputs(rule_schema)
  O = ob_map(rule_schema, :O)
  (ob_map(O, j) for (_, j) in named_ob_generators(shape(O)))
end

function named_ob_generators(C::FinCat)
  pairs = ((ob_generator_name(C, x), x) for x in ob_generators(C))
  Iterators.filter(pairs) do (name, x)
    # Ignore unnamed/anonymous generators.
    !(isnothing(name) || startswith(string(name), "##"))
  end
end


end # module 