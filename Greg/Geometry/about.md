# Formalizing geometry in Lean

## Goals
The goals of this project are the following:

- Learn how to define and use an axiomatic system in Lean
  * Best practices for structuring definitions and axioms to facilitate reuse and reduce boilerplate
  * Best practices for choosing formulations of defnitions and axioms

- Revisit Euclidean geometry as a theory
  * Investigate dependencies between theorems and axioms

## Approaches

1. Definition via 'axiom'
I found this approach in https://vaibhavkarve.github.io/leanteach_2020.html
However, I would like to have the ability to choose a model for the geometry and prove that the axioms hold for the model. I couldn't figure out how to do this, so I sought out another approach.

2. One big typeclass
the next approach i tried was to lump every definition and axiom into a single typeclass for lines and points. this turned out to not work well because such a grouping prevented me from using intermediate definitions, for example by defining a notion of parallel lines after defining a notion of lines going through a point, then using this notion to define euclid's 5th postulate. this approach would also make it impossible to only use part of the resulting theory, which would be desirable for slightly different (e.g. non-euclidean) geometries.

3. lots of small typeclasses
my current approach is to create a typeclass for every definition and axiom. this approach generally works well, although an amusing side-effect is that types must be passed manually into some definitions. for example, since no point is directly referenced in the proposition "lines l1 and l2 are parallel", but the notion of parallel lines depends on the type of point that said lines may pass through, the proposition requires an explicit type of point, e,.g. "lines l1 and l2 are parallel with respect to points of type p". another foreseeable quirk is the need to list out typeclasses explicitly.
