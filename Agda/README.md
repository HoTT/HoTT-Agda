Homotopy Type Theory in Agda
============================

Introduction
------------

This document describes the structure of the source code of this HoTT library in Agda. I have
written an introduction to Agda for homotopy type theorists in the `tutorial` directory containing
everything you need to know to understand the Agda code here, be sure to check it out.

Structure of the source
-----------------------

The structure of the source is roughly the following (sorted in topological order, every module only
depend on the modules listed before) :

### Base library

- `Types` contains the definitions of the basic types (universe levels, unit, empty, dependent sums,
  natural numbers, integers)
- `Functions` contains basic definitions about functions (composition, identities, constant maps)
- `Paths` contains the definitions and properties of paths types and the groupoid structure of
  types, transport of something in a fibration along a path and its various reduction rules, and
  other convenient constructions and properties
- `Contractible` contains some basic properties of contractible types (not needing the notion of
  equivalence)
- `Equivalences` contains the definition of equivalences and useful properties
- `Univalence` contains the statement of the univalence axiom
- `Funext` contains the proof of function extensionality (using univalence)
- `HLevel` contains various definitions and properties about h-levels
- `FiberEquivalences` contains the proof that a map between fibrations which is an equivalence of
  total spaces is a fiberwise equivalence (depends only on `Equivalences` and above)
- `Homotopy` exports everything above and is imported by every subsequent file

### Others

- `Integers.Integers` contains the definition of the successor function, the proof that it’s an
  equivalence, and the proof that the type of the integers is a set
- `Interval.Interval` contains the HIT definition of the interval
- `Interval.IntervalProps` contains the proof that the interval is contractible
- `Circle.Circle` contains the HIT definition of the circle
- `Circle.LoopSpace` contains the proof that the based loop space of the circle is equivalent to the
  type of the integers
