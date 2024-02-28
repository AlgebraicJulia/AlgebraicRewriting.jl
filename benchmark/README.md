# AlgebraicRewriting.jl benchmarks

This directory contains benchmarks for different parts of AlgebraicRewriting. To run all the
benchmarks, launch `julia --project=benchmark` and enter:

``` julia
using PkgBenchmark
import AlgebraicRewriting

benchmarkpkg(AlgebraicRewriting)
```

To run a specific set of benchmarks, use the `script` keyword argument, for
example:

``` julia
benchmarkpkg(AlgebraicRewriting; script="benchmark/Agents.jl")
```
