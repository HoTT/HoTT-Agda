Homotopy Type Theory in Agda
============================

Introduction
------------

This repository contains a development of homotopy type theory and univalent
foundations in Agda.  The structure of the source code is described below.

Agda Options
------------

This library is assuming the options `--universe-polymorphism` (on by default)
and the experimental one `--without-K`.

Style and naming conventions
----------------------------

### General

- Line length should be reasonably short, not much more than 80 characters
  (TODO: except maybe sometimes for equational reasoning?)
- Directories are in lowercase and modules are in CamelCase
- Types are Capitalized unless they represent properties (like `is-prop`)
- Terms are in lowercase-with-hyphens-between-words
- Try to avoid names of free variables in identifiers

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

There are also terms `⟨-1⟩`, `⟨0⟩`, `⟨1⟩`, `⟨2⟩` and `⟨_⟩ : ℕ → ℕ₋₂` with the
obvious definitions.

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

Structure of the source
-----------------------

The structure of the source is roughly the following:

### Old library (directory `old/`)

The old library is still present, mainly to facilitate code transfer to the new
library. Once everything has been ported to the new library, this directory will
be removed.

### Library (directory `lib/`)

The main library is more or less divided in three parts.

- The first part is exported in the module `lib.Basics` and contains everything
  needed to make the second part compile
- The second part is exported in the module `lib.types.Types` and contains
  everything you ever wanted to know about all type formers
- The third part contains more advanced stuff.

The whole library is exported in the file `HoTT`, so every file using the
library should contain `open import HoTT`.

TODO: describe more precisely each file

### Homotopy (directory `homotopy/`)

This directory contains proofs of interesting homotopy-theoretic theorems.

TODO: describe more precisely each file

### Experimental (directory `experimental/`)

This directory contains experimental things (as you can guess).

ACKNOWLEDGMENT
--------------

This material is partially based upon work supported by the National Science
Foundation under Grant Number 1116703. Any opinions, findings, and conclusions
or recommendations expressed in this material are those of the author(s)
and do not necessarily reflect the views of the National Science Foundation.
