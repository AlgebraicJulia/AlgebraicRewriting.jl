using AlgebraicRewriting
using Catlab, Catlab.CategoricalAlgebra, Catlab.Graphics, Catlab.Graphs

"""
This is a self-contained walkthrough of the main features of AlgebraicRewriting. 
This is a regular julia file that can be run interactively.

The VS Code REPL makes it easy to have figures automatically pop up in a side 
window, so this is the preferred way of interacting with this file. However, if 
that is not available, your options are to
1.) copy-paste the code into a Jupyter notebook 
2.) use the following `to_svg` function, which will write a graphviz output to 
    a SVG file and can be viewed in a browser.
"""

"""
The Julia pipe syntax |> allows you to easily append " |> to_svg " to a line
with a visualization.
"""
to_svg(G, filename="tmp.svg") = open(filename, "w") do io
    show(io, "image/svg+xml", G)
end

to_graphviz(path_graph(Graph, 3))  

