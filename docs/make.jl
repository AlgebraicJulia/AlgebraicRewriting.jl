using Documenter
using AlgebraicRewriting

makedocs(
    sitename = "AlgebraicRewriting",
    format = Documenter.HTML(),
    modules = [AlgebraicRewriting]
)

# Documenter can also automatically deploy documentation to gh-pages.
# See "Hosting Documentation" and deploydocs() in the Documenter manual
# for more information.
#=deploydocs(
    repo = "<repository url>"
)=#
