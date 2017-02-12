Homotopy Type Theory in Agda
============================
[![Build Status](https://travis-ci.org/HoTT/HoTT-Agda.svg)](https://travis-ci.org/HoTT/HoTT-Agda)

Introduction
------------

This repository contains a development of homotopy type theory and univalent
foundations in Agda.  The structure of the source code is described below.

Setup
-----

The code is loosely broken into `core` and `theorems` Agda libraries.
You need to include at least the path to `core.agda-lib` in your library list.
See `CHANGELOG` of Agda 2.5 for more information.

Agda Options
------------

Each Agda file should have `--without-K --rewriting` in the header.
`--without-K` is to restrict pattern matching so that the uniqueness of identity proofs is not admissible,
and `--rewriting` is for the computational rules of the points in higher inductive types.

Style and naming conventions
----------------------------

### General

- Line length should be reasonably short, not much more than 80 characters
  (TODO: except maybe sometimes for equational reasoning?)
- Directories are in lowercase and modules are in CamelCase
- Types are Capitalized unless they represent properties (like `is-prop`)
- Terms are in lowercase-with-hyphens-between-words
  unless the words refer to types.
- Try to avoid names of free variables in identifiers
- Pointedness and other disambiguating labels may be omitted if inferable from prefixes.

TODO: principles of variable names

### Identity type

The identity type is `_==_`, because `_=_` is not allowed in Agda. For every
identifier talking about the identity type, the single symbol `=` is used
instead, because this is allowed by Agda. For instance the introduction rule for
the identity type of Σ-types is `pair=` and not `pair==`.

### Truncation levels

The numbering is the homotopy-theoretic numbering, parametrized by the type
`TLevel` or `ℕ₋₂` where

    data TLevel : Type₀ where
      ⟨-2⟩ : TLevel
      S : TLevel → TLevel

    ℕ₋₂ = TLevel

Numeric literals (including negative ones) are overloaded.
There is also explicit conversion `⟨_⟩ : ℕ → ℕ₋₂` with the obvious definition.

### Properties of types

Names of the form `is-X` or `has-X`, represent properties that can hold (or not)
for some type `A`. Such a property can be parametrized by some arguments. The
property is said to hold for a type `A` iff `is-X args A` is inhabited. The
types `is-X args A` should be (h-)propositions.

Examples:

    is-contr
    is-prop
    is-set
    has-level       -- This one has one argument of type [ℕ₋₂]
    has-all-paths   -- Every two points are equal
    has-dec-eq      -- Decidable equality

- The theorem stating that some type `A` (perhaps with arguments) has some
  property `is-X` is named `A-is-X`. The arguments of `A-is-X` are the arguments
  of `is-X` followed by the arguments of `A`.
- Theorems stating that any type satisfying `is-X` also satisfies `is-Y` are
  named `X-is-Y` (and not `is-X-is-Y` which would mean `is-Y (is-X A)`).

Examples (only the nonimplicit arguments are given)

    Unit-is-contr : is-contr Unit
    Bool-is-set : is-set Bool
    is-contr-is-prop : is-contr (is-prop A)
    contr-is-prop : is-contr A → is-prop A
    dec-eq-is-set : has-dec-eq A → is-set A
    contr-has-all-paths : is-contr A → has-all-paths A

The term giving the most natural truncation level to some type constructor T is
called `T-level`:

    Σ-level : (n : ℕ₋₂) → (has-level n A) → ((x : A) → has-level n (P x))
           → has-level n (Σ A P)
    ×-level : (n : ℕ₋₂) → (has-level n A) → (has-level n B)
           → has-level n (A × B))
    Π-level : (n : ℕ₋₂) → ((x : A) → has-level n (P x))
           → has-level n (Π A P)
    →-level : (n : ℕ₋₂) → (has-level n B)
           → has-level n (A → B))

Similar suffices include `conn` for connectivity.

### Lemmas of types

Modules of the same name as a type collects useful properties
given an element of that type. Records have this functionality built-in.

### Functions and equivalences

- A natural function between two types `A` and `B` is often called `A-to-B`
- If `f : A → B`, the lemma asserting that `f` is an equivalence is called
  `f-is-equiv`.
- If `f : A → B`, the equivalence `(f , f-is-equiv)` is called `f-equiv`.
- As a special case of the previous point, `A-to-B-equiv` is usually called
  `A-equiv-B` instead.

We have

    A-to-B : A → B
    A-to-B-is-equiv : is-equiv (A-to-B)
    A-to-B-equiv : A ≃ B
    A-equiv-B : A ≃ B
    A-to-B-path : A == B
    A-is-B : A == B

Also for group morphisms, we have

    G-to-H : G →ᴳ H
    G-to-H-is-iso : is-equiv (fst G-to-H)
    G-to-H-iso : G ≃ᴳ H
    G-iso-H : G ≃ᴳ H

However, `A-is-B` can be easily confused with `is-X` above,
so it should be used with great caution.

Another way of naming of equivalences only specifies one side.
Suffixes `-econv` may be added for clarity.
The suffix `-conv` refers to the derived path.

    A : A == B
    A-econv : A ≃ B
    A-conv : A == B

TODO: `pres` and `preserves`.

TODO: `-inj` and `-surj` for injectivity and surjectivity.

TODO: `-nat` for naturality.

### Negative types

The constructor of a record should usually be the uncapitalized name of the
record. If `N` is a negative type (for instance a record) with introduction
rule `n` and elimination rules `e1`, …, `en`, then

- The identity type on `N` is called `N=`
- The intros and elim rules for the identity type on `N` are called `n=` and
  `e1=`, …, `en=`
- If necessary, the double identity type is called `N==` and similarly for the
  intros and elim.
- The β-elimination rules for the identity type on `N` are called `e1=-β`, …,
  `en=-β`.
- The η-expansion rule is called `n=-η` (TODO: maybe `N=-η` instead, or
  additionally?)
- The equivalence/path between `N=` and `_==_ {N}` is called
- `N=-equiv`/`N=-path` (TODO: `n=-equiv`/`n=-path` would maybe be more natural).
   Note that this equivalence is usually needed in the direction `N= ≃ _==_ {N}`

If a positive type `N` behaves like a negative one through
some access function `f : N → M`,
the property is called `f-ext : (n₁ n₂ : N) → f n₁ = f n₂ → n₁ = n₂`

### Functoriality

A family of some structures indexed by another structures
often behaves like a functor which maps functions between structures
to functions between corresponding structures.
Here is a list of standardized suffices that denote different kind of functoriality:

- `X-fmap`: `X` maps morphisms to morphisms (covariantly or contravariantly).
- `X-emap`: `X` maps isomorphisms to isomorphisms.
- `X-isemap`: Usually a part of `X-emap` which lifts the proof of being an isomorphism.

For types, morphisms are functions and isomorphisms are equivalences.
Bi-functors are not standardized (yet).

TODO: `X-fmap-id`, `X-fmap-∘`

### Precedence

Precedence convention

1. Separators ```_$_``` and arrows: 0
2. Layout combinators (equational reasoning): 10-15
3. Equalities, equivalences: 30
4. Other relations, operators with line-level separators: 40
5. Constructors (for example ```_,_```): 60
6. Binary operators (including type formers like ```_×_```): 80
7. Prefix operators: 100
8. Postfix operators: 120

### Inductive types and higher ones

- See ```core/lib/types/Pushout.agda``` for an example of higher inductive types.

- Constructors should make all the parameters implicit, and varients which make
  commonly specified parameters explicit should have the suffix ```'```.

- ```S0``` is defined as ```Bool```, and the circle is the suspension of ```Bool```.

### Type constructors

Several functions related to an arity-1 type constructor `N` should be named as follows:

- `equiv-N` which takes an equivalence between `A` and `B` to an equivalence between `N A` and `N B`.

### Algebraic rules

### Groups

Structure of the source
-----------------------

The structure of the source is roughly the following:

### Old code (directory `old/`)

The old library is still present, mainly to facilitate code transfer to the new
library. Once everything has been ported to the new library, this directory will
be removed.

### Core library (directory `core/`)

The main library is more or less divided in three parts.

- The first part is exported in the module `lib.Basics` and contains everything
  needed to make the second part compile
- The second part is exported in the module `lib.types.Types` and contains
  everything you ever wanted to know about all type formers
- The third part contains more advanced stuff.

The whole library is exported in the file `HoTT`, so every file using the
library should contain `open import HoTT`.

TODO: describe more precisely each file

### Homotopy (directory `theorems/homotopy/`)

This directory contains proofs of interesting homotopy-theoretic theorems.

TODO: describe more precisely each file

### Cohomology (directory `theorems/cohomology/`)

This directory contains proofs of interesting cohomology-theoretic theorems.

TODO: describe more precisely each file

### CW complexes (directory `theorems/cw/`)

This directory contains proofs of interesting theorems about CW complexes.

TODO: describe more precisely each file

### Experimental and unfinished (directory `stash/`)

This directory contains experimental or unfinished work.

Citation
--------

```
@online{hott-in:agda,
  author={Guillaume Brunerie
    and Kuen-Bang {Hou (Favonia)}
    and Evan Cavallo
    and Jesper Cockx
    and Christian Sattler
    and Chris Jeris
    and Michael Shulman
    and others},
  title={Homotopy Type Theory in {A}gda},
  url={https://github.com/HoTT/HoTT-Agda}
}
```

Names are roughly sorted by the amount of contributed code,
with the founder Guillaume always staying on the top.
List of contribution (possibly outdated or incorrect):

- Guillaume Brunerie: the foundation, pi1s1, 3x3 lemma, many more
- Favonia: covering space, Blakers-Massey, van Kampen, cohomology
- Evan Cavallo: cubical reasoning, cohomology, Mayer-Vietoris
- Jesper Cockx: rewrite rules
- Christian Sattler: updates to equivalence and univalence
- Chris Jeris: Eckmann-Hilton argument
- Michael Shulman: updates to equivalence and univalence

Funding
-------

This material is partially based upon work supported by the National Science
Foundation under Grant Number 1116703. Any opinions, findings, and conclusions
or recommendations expressed in this material are those of the author(s)
and do not necessarily reflect the views of the National Science Foundation.

This material is also partially based upon work supported by the Air Force
Office of Scientific Research under Multidisciplinary Research Program of
the University Research Initiative (MURI) Grant Number FA9550-15-1-0053.
