module TestPoly 

using Test
using AlgebraicRewriting, Catlab
using AlgebraicRewriting.Schedules.Poly: getvalue

# Maybe monad
#############
"""  ____
 ℕ -|    |- String 
 𝔹 -|S=ℕ |- Nothing
     -----
Machine receives a ℕ, it adds it to its internal state + returns nothing 
Machine recieves a 𝔹, it outputs symbol e.g. "True23" where the # is the state.
If the machine has state 10, it returns nothing.
"""
function ex_fun(S::Int, w::WireVal) 
  if S == 10 
    MealyRes(S, Nothing) 
  elseif w.wire_id == 1 
    MealyRes(S + w.val, [(nothing, WireVal(2, nothing))])
  else 
    MealyRes(S, [(nothing, WireVal(1, "$(w.val)$S"))])
  end 
end
m = Mealy(ex_fun, [Int, Bool], [String, Nothing], Maybe, 0)
t = BTree(m)
@test_throws ErrorException t([WireVal(1,true)])
(wv3, wv7),(wvt, wvf) = WireVal.(1, [3,7]), WireVal.(2, Bool[1,0])
@test isnothing(getvalue(last(only(t([wv3])))))
@test getvalue(last(only(t([wvf])))) == "false0"
@test getvalue(last(only(t([wv3, wvt])))) == "true3"
@test isempty(t([wv3, wv7, wvt]))
@test length(t.result_cache) == 5 # 3, f, 3+t, 3+7, 3+7+t

# List monad
############

"""  ____
 ℕ -|    |- String 
 𝔹 -|S=ℕ |- Nothing
     -----
Machine receives a ℕ, it adds it to its internal state + returns nothing 
Machine recieves a 𝔹, it outputs symbol e.g. "True23" where the # is the state.
If the boolean is false, it *also* outputs a nothing.
If the machine has state 10, it returns nothing.
"""
function ex_fun2(S::Int, w::WireVal) 
  if S == 10 
    MealyRes(S, Nothing) 
  elseif w.wire_id == 1 
    MealyRes(S+w.val, [(nothing, WireVal(2, nothing))]) 
  else 
    res = [(nothing, WireVal(1, "$(w.val)$S"))]
    w.val || push!(res, (nothing, WireVal(2,nothing)))
    MealyRes(S, res)
  end
end
m = Mealy(ex_fun2, [Int, Bool], [String, Nothing], List, 0)
t = BTree(m)
@test isnothing(getvalue(last(only(t([wv3])))))
@test getvalue(last(only(t([wv3, wvt])))) == "true3"
@test getvalue.(last.(t([wv3, wvf]))) == ["false3", nothing]

# Probability Monad 
####################

# ℕ → ℕ ⊗ ℕ --- Increment an integer +1 and +2, stateless
inc_fun(::Nothing, w::WireVal) = 
  MealyRes(nothing, [(p,WireVal(i,w.val+i)) for (i,p) in enumerate([1//3,2//3])])

mi = Mealy(inc_fun, [Int], [Int,Int], Dist, nothing, "M2")

# ℕ → ℕ ⊗ Str --- If even, decrement gas and send out, otherwise print str twice
function some_fun(S::Int,w::WireVal)::MealyRes{Int, Rational{Int}}
  if S <= 0 
    MealyRes(S, Rational{Int})
  elseif w.val % 2 == 0 
    MealyRes(S-1,[(1//1,WireVal(1,w.val))])
  else 
    MealyRes(S,[(p,WireVal(2, string(w.val))) for p in [1//3,2//3]])
  end
end

ms = Mealy(some_fun, [Int], [Int, String], Dist, 5, "M1")

wd = WiringDiagram([:N],[:S])
b1 = add_box!(wd, Box(ms,[:N],[:N,:S]))
b2 = add_box!(wd, Box(mi,[:N],[:N,:N]))
i, o = [(f(wd),1) for f in [input_id, output_id]]
add_wires!(wd, Pair[i=>(b1,1), (b1,1)=>(b2,1), (b1,2)=>o, (b2,1)=>(b1,1),(b2,2)=>(b1,1)])
# to_graphviz(wd; orientation=LeftToRight)

sim = Simulator(wd)


res = apply_schedule(sim, 0, Dist)
@test length(res) == 4




end # module
