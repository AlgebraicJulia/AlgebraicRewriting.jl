using Documenter
using AlgebraicRewriting

# Set Literate.jl config if not being compiled on recognized service.
config = Dict{String,String}()
if !(haskey(ENV, "GITHUB_ACTIONS") || haskey(ENV, "GITLAB_CI"))
  config["nbviewer_root_url"] = "https://nbviewer.jupyter.org/github/AlgebraicJulia/AlgebraicRewriting.jl/blob/gh-pages/dev"
  config["repo_root_url"] = "https://github.com/AlgebraicJulia/AlgebraicRewriting.jl/blob/main/docs"
end

makedocs(
    sitename = "AlgebraicRewriting",
    format = Documenter.HTML(),
    modules = [AlgebraicRewriting]
)


@info "Deploying docs"
deploydocs(
  target = "build",
  repo   = "github.com/AlgebraicJulia/AlgebraicRewriting.jl.git",
  branch = "gh-pages",
  devbranch = "main"
)