Homotopy Type Theory in Agda
============================

Introduction
------------

This repository contains a development of homotopy type theory and univalent
foundations in Agda.  The structure of the source code is described below.

There is also an introduction to Agda for homotopy type theorists in the
`tutorial` directory containing everything you need to know to understand the
Agda code here, be sure to check it out.

Style and naming conventions
----------------------------

### General

- Line length is capped at 80 characters
- Names of modules are in CamelCase
- Names of terms are in lowercase-with-hyphens-between-words
- There are a few sporadic exceptions to the previous rules, namely the type of
  universe levels `Level` (usually implicit) and universe-like types (`hProp`,
  `hSet`, `Type≤`, `pType`)
- Unicode chars can appear in names but should not be overused (prefer `A-to-B`
  to `A→B` for instance)
- Avoid names of free variables in identifiers
- Universe levels are usually implicit but should be explicit when they cannot
  be deduced from the context (for instance `pushout-diag i` is the type of
  pushout diagrams in the universe level `i`)

### Truncation levels

I’m not using the terminology of h-levels anymore, the `is-hlevel` term has been
replaced by `is-truncated`. The argument of `is-truncated` is of type `ℕ₋₂`
where

    data ℕ₋₂ : Set where
      ⟨-2⟩ : ℕ₋₂
      S : (n : ℕ₋₂) → ℕ₋₂

There are also terms `⟨-1⟩`, `⟨0⟩`, `⟨1⟩`, `⟨2⟩` and `⟨_⟩ : ℕ → ℕ₋₂` with the
obvious definitions.

### Properties of types

Names of the form `is-X` (or sometimes `has-X`), represent properties that can
hold (or not) for some type `A`. The property `is-X` can be parametrized by some
arguments. The property is said to hold for a type `A` iff `is-X args A` is
inhabited. The types `is-X args A` should be (h-)propositions.

Examples:

    is-contr
    is-prop
    is-set
    is-truncated    -- This one has one argument of type [ℕ₋₂]
    has-all-paths   -- Every two points are equal
    has-dec-eq      -- Decidable equality

- The theorem stating that some type `A` (perhaps with arguments) has some
  property `is-X` is named `A-is-X`. The arguments of `A-is-X` are the arguments
  of `is-X` followed by the arguments of `A`.
- It can be recursive (e.g. if `B` satisfies `is-X`, then so does `A B`) in
  which case the arguments of `A` that can be deduced from the recursive proofs
  of `is-X` are implicit in `A-is-X`.
- If `is-X` takes an argument which is a datatype and that the conclusion of the
  theorem is `is-X (c …) A` where `c` is a constructor of the type of the
  argument of `is-X`, then the theorem is called `A-is-X-c`.
- Theorems stating that any type satisfying `is-X` also satisfies `is-Y` are
  named `X-is-Y` (and not `is-X-is-Y` which would mean `is-Y (is-X A)`).

Examples (only the nonimplicit arguments are given)

    unit-is-contr : is-contr unit
    bool-is-set : is-set bool
    Σ-is-truncated : (n : ℕ₋₂)
      → (is-truncated n A → ((x : A) → is-truncated n (P x))
           → is-truncated n (Σ A P))
    ×-is-truncated : (n : ℕ₋₂)
      → (is-truncated n A → is-truncated n B → is-truncated n (A × B))
    Π-is-truncated : (n : ℕ₋₂)
      → ((x : A) → is-truncated n (P x)) → is-truncated n (Π A P)
    →-is-truncated : (n : ℕ₋₂) → (is-truncated n B → is-truncated n (A → B))
    is-contr-is-prop : is-contr (is-prop A)
    contr-is-prop : is-contr A → is-prop A
    truncated-is-truncated-S : (n : ℕ₋₂)
      → (is-truncated n A → is-truncated (S n) A)
    dec-eq-is-set : has-dec-eq A → is-set A
    contr-has-all-paths : is-contr A → has-all-paths A

### Functions and equivalences

- A natural function between two types `A` and `B` is often called `A-to-B`
- If `f : A → B`, the lemma asserting that `f` is an equivalence is called
  `f-is-equiv`
- If `f : A → B`, the equivalence `(f , f-is-equiv)` is called `f-equiv`
- As a special case of the previous point, `A-to-B-equiv` is usually called
  `A-equiv-B` instead

We have

    A-to-B : A → B
    A-to-B-is-equiv : is-equiv (A-to-B)
    A-to-B-equiv : A ≃ B
    A-equiv-B : A ≃ B

### Records

If `r` is a record, there is a lemma saying that if `u v : r` and that the
fields of `u` and `v` are respectively equal, then `u` and `v` are equal. This
lemma is called `r-eq-raw`.

This is usually not quite what is needed (we may want to replace equality of
types by equivalence and equality of functions by homotopy), this new lemma is
called `r-eq`.

Structure of the source
-----------------------

The structure of the source is roughly the following:

### Base library

- `Types` contains the definitions of the basic types (universe levels, unit,
  empty, dependent sums, natural numbers, integers, …)
- `Functions` contains basic definitions about functions (composition,
  identities, constant maps)
- `Paths` contains the definitions and properties of paths types and the
  groupoid structure of types, transport of something in a fibration along a
  path and its various reduction rules, and other convenient constructions and
  properties
- `HLevel` contains definitions and properties about truncation levels (not
  needing the notion of equivalence)
- `Equivalences` contains the definition of equivalences and useful properties
- `Univalence` contains the statement of the univalence axiom
- `Funext` contains the proof of function extensionality (using univalence)
- `HLevel` contains definitions and properties about truncation levels where the
  notion of equivalence or function extensionality is needed
- `FiberEquivalences` contains the proof that a map between fibrations which is
  an equivalence of total spaces is a fiberwise equivalence (depends only on
  `Equivalences` and above)
- `Base` exports everything above and is the file that should be imported in
  any file

- `Integers.Integers` contains the definition of the successor function, the
  proof that it’s an equivalence, and the proof that the type of the integers
  is a set

### Homotopy

The `Homotopy` directory contains homotopy-theoretic definitions and properties.
More precisely there is:

- `PullbackDef` contains the definition of the type that should satisfy the
  universal property of pullback in the universes `Set i`
- `PullbackUP` contains the definition of what it means for some type to satisfy
  the universal property of pullback inside some subcategory (parametrized by a
  `P : Set i → hProp i`)
- `PullbackIsPullback` contains a proof that what should be a pullback in
  `Set i` is indeed a pullback
- Similarly for `PushoutDef`, `PushoutUP` and `PushoutIsPushout`. The file
  `PushoutUP` also contains a proof that two pushouts of the same diagram are
  equivalent
- `TruncatedHIT` contains the proof that an HIT with special constructors that
  fill spheres can be given an elimination rule easier to work with (see
  `Algebra.FreeGroup` for an example)
- `TruncationHIT` contains the HIT defining the truncation, with a small hack to
  handle (-2)-truncations
- `Truncation` contains a nicer interface for truncation and the universal
  property (this is the file you should import if you want to do anything with
  truncations)

### Spaces

The `Spaces` directory contains definitions and properties of various spaces.

- `Interval` contains the definition of the interval
- `IntervalProps` contains a proof that the interval is contractible and that
  the interval implies (non-dependent) function extensionality
- `Circle` contains the HIT definition of the circle
- `LoopSpaceCircle` contains the proof that the based loop space of the circle
  is equivalent to the type of the integers
- `Suspension` contains the definition of the suspension of a type (as a
  special case of pushout)
- `Spheres` contains the definitions of spheres
- `WedgeCircles` contains the definition of the wedge of a set of circles
- `FlatteningLoopSpaceWedgeCircles` contains the proof of the flattening lemma
  for the loop space of a wedge of circles (indexed by a set)
- `LoopSpaceDecidableWedgeCircles` contains the proof that the loop space of a
  wedge of circles indexed by a set with decidable equality is the free group

### Algebra

The `Algebra` directory contains some basic algebra.

- `Groups` contains a crappy definition of groups
- `GroupIntegers` contains a proof that the integers form a group
- `FreeGroup` contains the definition of the free group on a set of generators
  (not that it’s a group, actually)
- `FreeGroupProps` contains properties of the free group (that it’s a set and
  that multiplying by a generator is an equivalence)
- `F2NotCommutative` contains a proof that F2 is not commutative
- `FreeGroupAsReducedWords` contains an equivalent definition of the free group
  as a set of reduced words, in the case where the set of generators has
  decidable equality

### Sets

The `Sets` repository contains properties of the category of (h)sets.

- `Quotient` contains a definition of the quotient of a set by a (prop-valued)
  equivalence relation with truncated higher inductive types
- `QuotientUP` proves the universal property of quotients

Copyrights
----------

The equational reasoning combinators are adapted from
[Nils Anders Danielsson's library](http://www.cse.chalmers.se/~nad/repos/equality/)
which is released under BSD3.
