module TestStructuredCospans

using Test
using Catlab, Catlab.Theories, Catlab.Graphs
using Catlab.CategoricalAlgebra: @acset, @acset_type, FinFunction, FinSet, apex, terminal, OpenCSetTypes, Span, nparts, ACSetTransformation, CSetTransformation
using AlgebraicRewriting

# Horizontal composition of epidemiological model rewrites
#---------------------------------------------------------

@present TheoryPetriNet(FreeSchema) begin
  (T,S,I,O)::Ob
  it::Hom(I,T)
  is::Hom(I,S)
  ot::Hom(O,T)
  os::Hom(O,S)
end

@acset_type PetriNet(TheoryPetriNet);

const OpenPetriNetOb, OpenPetriNet = OpenCSetTypes(PetriNet,:S);
ns = x->nparts(x,:S)
Open(p::PetriNet) = OpenPetriNet(p, map(x->FinFunction([x], ns(p)), 1:ns(p))...);
Open(p::PetriNet, legs...) = OpenPetriNet(p, map(l->FinFunction(l, ns(p)), legs)...);
Open(n, p::PetriNet, m) = Open(p, n, m);
o1, o2 = OpenPetriNetOb(1), OpenPetriNetOb(2);
L = typeof(o1).parameters[1]
v1, v2 = idV_(o1), idV_(o2);
i1, i2, i3 = (id(FinSet(x)) for x in 1:3)
idH_(o1); # test if it fails

isquare = id2_(o1);
composeV_(isquare, isquare)

iv2 = id2H_(Span(i1,i1), o1);

SIR = @acset PetriNet begin # S ->[si]⇉← I → R
    S = 3 # S I R
    T = 2 # si ir
    I = 3
    O = 3
    it = [1,2,1]
    ot = [1,2,1]
    is = [1,2,2]
    os = [2,3,2]
end;
oSIR = Open([1], SIR, [2,3]);
ioSIR = id2V_(oSIR);

SEIR = @acset PetriNet begin # S ->[si]⇉← I → R
    S = 4 # S I R E
    T = 3 # si ir ei
    I = 4
    O = 4
    it = [1,2,1,3]
    ot = [1,2,1,3]
    is = [1,2,2,4]
    os = [2,3,4,2]
end;
oSEIR = Open([1], SEIR, [2,3]);
# SIR minus one of the infection arrows to I
# which will instead be going to E
sirOverlap = @acset PetriNet begin
    S = 3 # S I R
    T = 2 # si ir
    I = 3
    O = 2
    it = [1,2,1]
    ot = [1,2]
    is = [1,2,2]
    os = [2,3]
end;
osirOverlap = Open([1], sirOverlap, [2,3]);
sirUp = ACSetTransformation(sirOverlap, SIR,
    S=[1,2,3],T=[1,2],I=[1,2,3],O=[1,2]);
sirDown = ACSetTransformation(sirOverlap, SEIR,
    S=[1,2,3],T=[1,2],I=[1,2,3],O=[1,2]);

expose_up = StructuredMultiCospanHom(osirOverlap, oSIR, [sirUp, L(i1), L(i2)]);
expose_down = StructuredMultiCospanHom(osirOverlap, oSEIR,
                                       [sirDown, L(i1), L(i2)]);
expose = openrule(Span(expose_up, expose_down));


IQR = @acset PetriNet begin # I -> Q -> R
    S = 3 # I Q R
    T = 2 # iq qr
    I = 2
    O = 2
    it = [1, 2]
    ot = [1, 2]
    is = [1, 2]
    os = [2, 3]
end;
oIQR = Open([1,3],IQR, [2]);

IQRescape = @acset PetriNet begin # I ↔ Q -> R
    S = 3 # I Q R
    T = 3 # iq qr qi
    I = 3
    O = 3
    it = [1, 2, 3]
    ot = [1, 2, 3]
    is = [1, 2, 2]
    os = [2, 3, 1]
end;
oIQRescape = Open([1,3],IQRescape, [2]);

IQRinj = ACSetTransformation(IQR, IQRescape,
    S=[1,2,3], T=[1,2], I=[1,2], O=[1,2]);

escape_up = left(id2V_(oIQR).data)
escape_down = StructuredMultiCospanHom(oIQR, oIQRescape, ACSetTransformation[IQRinj, right(v2), right(v1)])
escape = openrule(Span(escape_up, escape_down))

# WRITE REWRITE RULES FOR THESE TWO COMPONENTS INDIVIDUALLY
# CAN COMBINE INTO A LARGER REWRITE RULE
expose_escape = composeH_(expose, escape); # exposes S and Q
bottom = apex(right(expose_escape.data).tgt)
expected_bottom = @acset PetriNet begin
  S = 5 # S I R E Q
  T = 6; O = 7; I = 7
      # si ir ei iq qr qi
  it = [1,1,2, 3, 4, 5, 6]
  ot = [1,1,2, 3, 4, 5, 6]
  is = [1,2,2, 4, 2, 5, 5]
  os = [2,4,3, 2, 5, 3, 2]
end
@test is_isomorphic(bottom, expected_bottom)

# Program optimization example
#-----------------------------
# Rewrite ⦿→□→⦿→□→⦿ into ⦿→□→⦿
# Dangling condition prevents us from applying this where compression is invalid
o_interface = Open([1], L(FinSet(2)), [2])
a_pattern = @acset PetriNet begin
  S = 3; T = 2; I = 2; O = 2
  is = [1,2]; it = [1,2]; ot = [1,2]; os = [2,3]
end
a_result = @acset PetriNet begin
  S=2; T=1; I=1; O=1; is=1; it=1; ot=1; os=2
end
o_pattern = Open([1], a_pattern, [3])
o_result = Open([1], a_result, [2])
o_up = ACSetTransformation(L(FinSet(2)), a_pattern, S=[1,3])
o_down =ACSetTransformation(L(FinSet(2)), a_result, S=[1,2])
L_morph = StructuredMultiCospanHom(o_interface, o_pattern, [o_up, L(i1), L(i1)])
c_rule = openrule(Span(L_morph,
  StructuredMultiCospanHom(o_interface, o_result, [o_down, L(i1), L(i1)])))

#  1 a 2 b 3 c 4 d 5
#  ⦿→□→⦿→□→⦿→□→⦿→□→⦿
#   ↘           ↘
#6 ⦿←□  e     f □→⦿ 7
# The first branch does NOT impede rewriting top row
# But the second branch does
prog = @acset PetriNet begin
  S = 7; T = 6; I = 6; O = 6
  is = [1,2,3,4,1,4]
  it = [1,2,3,4,5,6]
  ot = [1,2,3,4,5,6]
  os = [2,3,4,5,6,7]
end
o_prog = Open([1],prog,[3])

# After applying two rewrites, the result should be
#  1 a 2 b 3
#  ⦿→□→⦿→□→⦿
#   ↘   ↘
#4 ⦿←□   □→⦿ 5

expected2 = @acset PetriNet begin
  S = 5; T = 4; I = 4; O = 4
  is = [1,2,1,2]
  it = [1,2,3,4]
  ot = [1,2,3,4]
  os = [2,3,4,5]
end

# However, we can only apply one rewrite unless we change the new interface
#  1 a 2 b 3 c 4
#  ⦿→□→⦿□→⦿→□→⦿
#   ↘      ↘
#5 ⦿←□ d  e □→⦿ 6

expected2 = @acset PetriNet begin
  S = 6; T = 5; I = 5; O = 5;
  is = [1,2,3,1,3]
  it = [1,2,3,4,5]
  ot = [1,2,3,4,5]
  os = [2,3,4,5,6]
end


@test length(open_homomorphisms(o_pattern, o_prog)) == 1
m = open_homomorphisms(o_pattern, o_prog)[1].maps[1];
l = left(c_rule.data).maps[1];
@test is_isomorphic(apex(open_rewrite(c_rule, o_prog)), expected2)

# Rewriting
###########
const OpenGraphOb, OpenGraph = OpenCSetTypes(Graph, :V)

# EXAMPLE GRAPHS
#---------------
G1,G2,G3 = Graph.(1:3)
Loop = apex(terminal(Graph))
Arrow = path_graph(Graph, 2)
BiArrow = @acset Graph begin V=2; E=2; src= [1,2]; tgt=[2,1] end
Three = @acset Graph begin V=3; E=2; src=[1,2]; tgt=[2,3] end
Square = @acset Graph begin V=4; E=4; src=[1,1,2,3]; tgt=[2,3,4,4] end
Tri = @acset Graph begin V=3; E=3; src=[1,1,2]; tgt=[2,3,3] end
LoopTri = @acset Graph begin V=3; E=4; src= [1,1,1,2]; tgt = [1,2,3,3] end

"""
  3→4
 ╱  ↓
1→2→5
"""
Trap = @acset Graph begin V=5;E=5;src=[1,2,1,3,4]; tgt=[2,5,3,4,5] end
CSpan = @acset Graph begin V=3; E=2; src=[1,3]; tgt=[2,2] end
Cycle = @acset Graph begin V=2; E=2; src=[1,2]; tgt=[2,1] end

# Example Spans
#--------------

id_1 = id(Graph(1));
id_2 = id(Graph(2));
flip = CSetTransformation(G2, G2, V=[2,1]);
f12 = CSetTransformation(G1, G2, V=[1]);
f22 = CSetTransformation(G1, G2, V=[2]);

sp1 = Span(id_1, id_1);
sp2 = Span(id_2, id_2);
flipflip = Span(flip, flip);

# Open Graphs
#------------
o1 = OpenGraph(G1, id_1[:V], id_1[:V]);
o2 = OpenGraph(G2, f12[:V], f22[:V]);
openloop = OpenGraph(Loop, id_1[:V], id_1[:V]);
openp2 = OpenGraph(path_graph(Graph, 3),
                   FinFunction([1], 3), FinFunction([3], 3))

openarr = OpenGraph(Arrow, f12[:V], f22[:V]);
openarr21 = OpenGraph(Arrow, id_2[:V], f22[:V]);
open3 = OpenGraph(Three,
                  FinFunction([2,1], 3),
                  FinFunction([3,2], 3));
opensquare = OpenGraph(Square,
                       FinFunction([1], 4),
                       FinFunction([2], 4));
opensquare2 = OpenGraph(Square,
                        FinFunction([1], 4),
                        FinFunction([4], 4));
opentrap = OpenGraph(Trap,
                     FinFunction([1,2], 5),
                     FinFunction([2,5], 5));
opencspan = OpenGraph(CSpan,
                        FinFunction([2,1], 3),
                        FinFunction([2], 3));
opencycle = OpenGraph(Cycle,  flip[:V], f22[:V]);

# Graph Transformations
#----------------------
gm1 = ACSetTransformation(G1, Loop, V=[1]);
up_ = ACSetTransformation(G2, Arrow, V=[1,2]);
down_ = ACSetTransformation(G2, G1, V=[1,1]);
tosquare = ACSetTransformation(Three, Square, V=[1,2,4],E=[1,3]);
totrap = ACSetTransformation(Three, Trap, V=[1,2,5], E=[1,2]);
tocspan = ACSetTransformation(Arrow, CSpan, V=[1,2], E=[1]);
tocycle = ACSetTransformation(Arrow, Cycle, V=[1,2], E=[1]);

rem_loop_l = StructuredMultiCospanHom(o1,
  openloop, ACSetTransformation[gm1, id_1, id_1])
triv = StructuredMultiCospanHom(o1, o1,
  ACSetTransformation[id_1, id_1, id_1])
squash_l = StructuredMultiCospanHom(o2, openarr,
  ACSetTransformation[up_, id_1, id_1])
squash_r = StructuredMultiCospanHom(o2, o1,
  ACSetTransformation[down_, id_1, id_1])
rem_loop = openrule(Span(rem_loop_l, triv))
add_loop = openrule(Span(triv, rem_loop_l))
squash = openrule(Span(squash_l, squash_r))
square_m = StructuredMultiCospanHom(openarr, opensquare,
  ACSetTransformation[ACSetTransformation(Arrow, Square, V=[1,2], E=[1]), id_1, id_1])

res = open_rewrite_match(squash, square_m)
@test is_isomorphic(apex(res), Tri)

res = open_rewrite_match(composeV_(squash, add_loop), square_m)
@test is_isomorphic(apex(res), LoopTri)

sqsq = composeH_(squash, squash); # squashes a path of length 2 into a point
sqsq_m = StructuredMultiCospanHom(openp2, opensquare2,
  ACSetTransformation[ACSetTransformation(
    path_graph(Graph, 3), Square, V=[1,2,4], E=[1,3]), id_1, id_1])
res = open_rewrite_match(sqsq, sqsq_m)
# squash one path of a commutative square and obtain •⇆•
@test is_isomorphic(apex(res), BiArrow)

end # module
