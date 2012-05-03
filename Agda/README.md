Homotopy Type Theory in Agda
============================

Introduction to Agda
--------------------

I have written an introduction to Agda for homotopy type theorists in the `tutorial` directory
containing everything you need to know to understand the Agda code here, be sure to check it out.

Structure of the source
-----------------------

The structure of the source is roughly the following (sorted in topological order, the files only
depend of files before) :

- `Types` contains the definitions of the basic types
- `Paths` contains the definitions and properties of paths types, transport of something in a
  fibration along a path, and the various reduction rules of `transport`
- `Contractible` contains some basic properties of contractible types (not needing the notion of
  equivalence)
- `Equivalences` contains the definition of equivalences and useful properties
- `Univalence` contains the statement of the univalence axiom
- `Funext` contains the proof of function extensionality (using univalence)
- `HLevel` contains various definitions and properties about h-levels
- `Homotopy` exports everything above

- `FiberEquivalences` contains the proof that a map between fibrations which is an equivalence of
  total spaces is a fiberwise equivalence (it only depends on `Equivalences` (and `Paths` and
  `Types`)).

