module TestIHS

using Test, AlgebraicRewriting, Catlab, nauty_jll

########################
# Directed Multigraphs #
########################
grph(x) = to_graphviz(x; node_labels=true, edge_labels=true)

NV = 2
rg(i::Int, j=nothing) = let j = isnothing(j) ? 2*i : j; @acset Graph begin 
  V=i; E=j; src=rand(1:i, j); tgt=rand(1:i, j)
end end

random_monic(n::Int; j=nothing) = 
  hom(rand(subobject_graph(rg(n, j))[2][2:end-1]))

# Example rewrites
####################

X = path_graph(Graph, 3)
L = path_graph(Graph, 2)
R = @acset Graph begin V=3; E=3; src=[1,1,2]; tgt=[2,3,3] end
f = homomorphism(L, R; initial=(V=[1,3],))
G = path_graph(Graph, 4)
m = homomorphism(L, G; initial=(E=[2],))
ihs = IHS(X, f, G);

rewrite!(ihs, [m], [f])

@test validate(ihs)

AlgebraicRewriting.Incremental.IHSData.to_datalog_json(
  ihs, "cache/test.json"; rename=(E=:edge,))


X = path_graph(Graph, 3)
f2 = homomorphism(Graph(2), L; monic=true, any=true)
G = Graph(3)
ms = [ACSetTransformation(Graph(2), Graph(3); V=x) for x in [[1,2],[2,3]]]
ihs = IHS(X,[f2], G);
rewrite!(ihs, ms, [f2,f2])
@test validate(ihs)


# Non-monic
#----------
X = path_graph(Graph, 3)
L = path_graph(Graph, 2)
R = @acset Graph begin V=3; E=3; src=[1,1,2]; tgt=[2,3,3] end
f = homomorphism(L, R; initial=(V=[1,3],))
G = @acset Graph begin V=2; E=2; src=[1,2]; tgt=2 end
m = homomorphism(L, G; initial=(E=[2],))

ihs = IHS(X,f, G);
Δ, H, ms = rewrite!(ihs, [m], [f])
@test length(matches(ihs)) == 7
@test validate(ihs)

# Random
#--------

NR = 2
for _ in 1:5
while true
  R = rg(NV)
  random_rule = hom(rand(subobject_graph(R)[2][2:end-2])) 
  random_pattern, random_state = rg(NV+1,NV+1), rg(NV+3,NV+3)
  random_match = homomorphism(dom(random_rule), random_state; 
                              random=true, any=true)
  isnothing(random_match) && continue
  hset = IHS(random_pattern, [random_rule], random_state);
  rewrite!(hset, [random_match], [random_rule])
  try validate(hset)
    println("SUCCESS: $(length(matches(hset)))")
  catch e
    show(stdout,"text/plain",dom(random_rule)) 
    show(stdout,"text/plain",R) 
    @show components(random_rule)
    show(stdout,"text/plain", random_state) 
    println.(random_matches)
    throw(e)
  end
  break
end
end

# Batch application
###################

X = path_graph(Graph, 3)
L1 = path_graph(Graph, 2)
R1 = @acset Graph begin V=3; E=3; src=[1,1,2]; tgt=[2,3,3] end
f1 = homomorphism(L1, R1; initial=(V=[1,3],))
f2 = homomorphism(Graph(2), L; monic=true, any=true)
G = @acset Graph begin V=3; E=1; src=1; tgt=2 end
ms = [homomorphism(L1, G; initial=(E=[1],)),
      ACSetTransformation(Graph(2), G; V=[2,3])]
ihs = IHS(X,[f1,f2], G);
Δ, H, new_ms = rewrite!(ihs, ms, [f1,f2])
@test validate(ihs)

# Pattern 
#--------
X = path_graph(Graph, 4)

# Rules
#------
L = path_graph(Graph, 2)
R = @acset Graph begin V=3; E=3; src=[1,1,2]; tgt=[2,3,3] end
f1 = homomorphism(L, R; initial=(V=[1,3],))
f2 = homomorphism(Graph(2), L; monic=true, any=true)

# Runtime data
#--------------
G = @acset Graph begin V=6; E=4; src=[1,2,3,5]; tgt=[2,3,4,6] end
rs = [f1,f2,f2]
ms = [homomorphism(L, G; initial=(E=[1],)), 
          ACSetTransformation.([(V=[5,1],),(V=[4,6],)],Ref(Graph(2)),Ref(G))...]
# Rewrite incrementally
#----------------------
ihs = IHS(X, [f1,f2], G);
rewrite!(ihs, ms, rs)
@test validate(ihs)

# Non-monic
#-----------
X = path_graph(Graph, 4)
G = @acset Graph begin V=3; E=2; src=[1,1]; tgt=[1,2] end
rs = [f1,f2]
ms = [homomorphism(L, G; initial=(E=[1],)), 
      ACSetTransformation(Graph(2),G; V=[2,3])]

ihs = IHS(X,[f1,f2], G);
@time rewrite!(ihs, ms, rs; optimize=true);

AlgebraicRewriting.Incremental.IHSModify.add_state!(ihs, G, 1) # reset
@time rewrite!(ihs, ms, rs; optimize=false);

@test validate(ihs)


# Random
#--------

NR = 2
for _ in 1:5
while true 
  R = rg(NV)
  random_rule = hom(rand(subobject_graph(R)[2][2:end-2])) 
  random_pattern, random_state = rg(NV+1,NV+1), rg(NV+3,NV+3)
  random_matches = [homomorphism(dom(random_rule), random_state; random=true, any=true) for _ in 1:NR]
  any(isnothing, random_matches) && continue
  hset = IHS(random_pattern, [random_rule], random_state);
  rewrite!(hset, random_matches, fill(random_rule, NR))
  try validate(hset)
    println("SUCCESS: $(length(matches(hset)))")
  catch e
    show(stdout,"text/plain",dom(random_rule)) 
    show(stdout,"text/plain",R) 
    @show components(random_rule)
    show(stdout,"text/plain", random_state) 
    println.(random_matches)
    throw(e)
  end
  break
end
end
##############################
# Discrete Dynamical Systems #
##############################

@present SchDDS(FreeSchema) begin X::Ob; Φ::Hom(X,X) end
@acset_type DDS(SchDDS, index=[:Φ])
DDS(i::Int) = @acset DDS begin X=i; Φ=[rand(1:i) for _ in 1:i] end
DDS(v::Vector{Int}) = @acset DDS begin X=length(v); Φ=v end

# One at a time
###############

X=DDS([1, 1, 1])
L=DDS([1])
R=DDS([1,1])
stat=DDS([1,1])
f=ACSetTransformation(L,R;X=[1])
m=ACSetTransformation(L,stat;X=[1])
ihs = IHS(X,[f],stat);
nm = rewrite!(ihs, [m], [f]);
validate(ihs)

# In this scenario, the ONLY way for there to be new morphisms is for the match morphism to not be monic

P = DDS([1,1])
L = DDS([1,1])
R = DDS([1,1,2])
stat = DDS([1])
f = homomorphism(L,R; initial=(X = [1, 2],))
m = homomorphism(L, stat; any=true)
ihs = IHS(P, [f], stat)
rewrite!(ihs, [m], [f]);
validate(ihs)



# Batch
#######

X=DDS([1, 1, 1])
L=DDS([1])
R=DDS([1,1])
stat=DDS([1,1])
f=ACSetTransformation(L,R;X=[1])
m=ACSetTransformation(L,stat;X=[1])
ihs = IHS(X,[f],stat);
m1 = homomorphism(L, stat)
nm = rewrite!(ihs, [m,m], [f,f]);
validate(ihs)

# Random
#-------
N = 3
for _ in 1:5
  while true 
    Rs = [DDS(N) for _ in 1:2]
    rules = [
      homomorphism(DDS(N), DDS(N+2); random=true, any=true, monic=true) 
      for _ in 1:2]
    random_rules = rand(rules, 2) # two of the rules
    any(isnothing,random_rules) && continue
    length(random_rules) == length(unique(random_rules)) || continue
    random_rules = Vector{ACSetTransformation}(random_rules)
    random_pattern, random_state = DDS(N+2), DDS(N+4)
    random_matches = [homomorphism(dom(r), random_state; any=true) for r in random_rules]
    any(isnothing, random_matches) && continue
    hset = IHS(random_pattern, random_rules, random_state);

    rewrite!(hset, random_matches, random_rules)
    validate(hset)
    println("SUCCESS $(length(matches(hset)))")
    break
  end
end

###############################
# (For visually debugging DDS)#
###############################

function to_grph(d::DDS)
  @acset Graph begin
    V=nparts(d, :X); E=nparts(d,:X); src=parts(d,:X); tgt=d[:Φ] 
  end
end
grph_dds(d::DDS) = to_grph(d) |> grph

function grph_dds(d::ACSetTransformation)
  grph(ACSetTransformation(to_grph(dom(d)), to_grph(codom(d)); V=d[:X], E=d[:X]))
end


# Datalog examples
###################

# Transitive closure
@present SchPath <: SchGraph begin 
  Path::Ob 
  (psrc, ptgt)::Hom(Path, V)
end

@acset_type Pth(SchPath) 

L = @acset Pth begin V=3; E=1; Path=1; src=2; tgt=3; psrc=1; ptgt=2 end
R = @acset Pth begin V=3; E=1; Path=2; src=2; tgt=3; psrc=1; ptgt=[2,3] end
f = homomorphism(L,R)

X = G = L

ihs = IHS(X,f, G);

get_cases(ihs; quotient=true) |> length

c = get_cases(ihs; quotient=true)

end # module
