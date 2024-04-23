# Constrained alternates graph solver

I wrote this as a side project in a few days to test out an idea

It should work on any system that can be turned into an acgraph

Note: I *really* don't care if you don't like my lisp writing style

# Future work

Add more object <-> acgraph converters

Add tests to determine whether the failure rate of the `acgraph-reduce/unitize!` reducer is higher than the `acgraph-reduce/eliminate!` reducer (I imagine it is, since `/unitize!` adds more information to the system than `/eliminate!`)

Write a system for more efficient reduction-informed constraint propagation. ie: Only propagate constraints for changed nodes

Possibly write a system (or at least explore writing a system) that uses generic set objects rather than vectors for alternates sets which would enable using nonfinite sets of alternates (though this would only work with the `/unitize!` reducer for obvious reasons)