using Pkg, Coverage

bashit(str) = run(`bash -c "$str"`)

bashit(""" find . -name '*.jl' -print0 | xargs -0 sed -i "" "s/^using Revise/# using Revise/g" """)

Pkg.test("AlgebraicRewriting"; coverage=true)
coverage = process_folder()
open("lcov.info", "w") do io
    LCOV.write(io, coverage)
end;
bashit("find . -name *.cov -delete")

