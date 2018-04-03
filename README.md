Homotopy Type Theory in Agda
============================
[![Build Status](https://travis-ci.org/HoTT/HoTT-Agda.svg)](https://travis-ci.org/HoTT/HoTT-Agda)

This repository contains a development of homotopy type theory and univalent
foundations in Agda.  The structure of the source code is described below.

Setup
-----

The code is loosely broken into `core` and `theorems` Agda libraries.
You need Agda 2.5.3 or newer
and include at least the path to `core.agda-lib` in your Agda library list.
See `CHANGELOG` of Agda 2.5 for more information.

Agda Options
------------

Each Agda file should have `--without-K --rewriting` in its header.
`--without-K` is to restrict pattern matching so that the uniqueness of identity proofs is not admissible,
and `--rewriting` is for the computational rules of the higher inductive types.

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
- `X-csmap`: `X` maps commuting squares to commuting squares (covariantly or contravariantly).
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

- `3x3/`: Contains definitions and lemmas for the 3x3-lemma stating that pushouts commute with pushouts.
  - `Commutes`: Proves the main result of the 3x3-lemma, see [Guillaume Brunerie's thesis][guillaume-brunerie-thesis].
- `AnyUniversalCoverIsPathSet`: Proves that for any universal covering `F` over some type `A` with base point `a₁ : A`, the fiber `F.Fiber a₂` over some point `a₂ : A` is equivalent to `a₁ =₀ a₂`, the 0-truncation of the space of paths between `a₁` and `a₂`.
- `BlakersMassey`: Contains a proof of the Blakers–Massey theorem. See the paper [A mechanization of the Blakers-Massey connectivity theorem in Homotopy Type Theory](https://arxiv.org/abs/1605.03227) and [Favonia's thesis][favonia-thesis].
- `blakersmassey/`: Contains definitions and lemmas for `BlakersMassey.agda`.
- `Bouquet`: Defines the bouquet of a family of circles and other families of pointed types.
- `CircleCover`: Defines a type `S¹Cover` and proves that it is equivalent to the type `Cover S¹ j` of coverings of `S¹`.
- `CircleHSpace`: Defines `⊙S¹-hSpace : HSpaceStructure ⊙S¹`.
- `CoHSpace`: Defines what a `CoHSpaceStructure` is.
- `CofiberComp`: Let `f : X ⊙→ Z` and `g : Y ⊙→ Z` be two pointed maps. This file proves that the cofiber of the composition of `g` and ```⊙cfcod` f : Z ⊙→ ⊙Cofiber f``` is equivalent to the cofiber of the induced map `h : X ⊙∨ Y ⊙→ Z`.
- `CofiberSequence`: Proves that the 5-term sequence obtained from a map `f : X ⊙→ Y` by repeatedly taking the map into the cofiber of the previous map is equivalent to the sequence ```X ⊙→⟨ f ⟩ Y ⊙→⟨ ⊙cfcod` f ⟩ ⊙Cofiber f ⊙→⟨ ⊙extract-glue ⟩ ⊙Susp X ⊙→⟨ ⊙Susp-fmap f ⟩ ⊙Susp Y ⊙⊣|```.
- `Cogroup`: Defines `CogroupStructure`, proves that such a structure on `X` induces a `GroupStructure` on `X ⊙→ Y` for any pointed type `Y`.
- `ConstantToSetExtendsToProp`: Proves that any constant function `f : A → B` factors through a function `Trunc -1 A → B`.
- `DisjointlyPointedSet`: Defines properties `is-separable X` (equality to the base point is decidable) and `has-disjoint-pt` (being pointedly equivalent to the coproduct of the singleton and `MinusPoint X`, that is `X` without the base point) of pointed types `X` and proves that they are equivalent. Also gives a pointed equivalence between `⊙Bouquet (MinusPoint X) 0`, a bouquet of 0-spheres indexed by `MinusPoint X` and `X` for each pointed type `X` that is separable.
- `elims/`: Contains proofs of elimination principles.
  - `CofPushoutSection`: Given a span `s`, in which one of the maps has a left-inverse, and a map `h : Pushout s → D`, proves an elimination principle for `Cofiber h`.
  - `Lemmas`: Contains technical lemmas about commutative squares over commutative squares.
  - `SuspSmash`: Gives an elimination principle for `Susp (X ∧ Y)`, the suspension of the smash product.
- `EM1HSpace`: Defines the `HSpaceStructure` on the Eilenberg–MacLane space `⊙EM₁ G` for an abelian group `G`.
- `EilenbergMacLane`: Defines the Eilenberg–MacLane spaces `⊙EM G n`, proves that `⊙Ω (⊙EM G (S n))` is pointedly equivalent to `⊙EM G n` for each `n` and that their homotopy groups are as required. See *Eilenberg-MacLane Spaces in Homotopy Type Theory* by Dan Licata and Eric Finster.
- `EilenbergMacLane1`: Proves that the fundamental group of the Eilenberg–MacLane space `⊙EM₁ G` (which is defined as a HIT) is in fact `G`.
- `FiberOfWedgeToProduct`: Let `X` of `Y` be two types with basepoints `x₀` and `y₀`. This contains a proof that the fiber of the induced map `X ∨ Y → X × Y` over a point `(x , y)` is equivalent to the join `(x₀ == x) * (y₀ == y)`.
- `FinWedge`: Contains helper functions and lemmas for dealing with wedges indexed over `Fin I` for some `I : ℕ`.
- `Freudenthal`: Proves the Freudenthal suspension theorem.
- `GroupSetsRepresentCovers`: Let `X` be a 0-connected type. This file gives an equivalence between coverings of `X` and `πS 0 X`-sets (where `πS 0 X` is the fundamental group of `X`).
- `HSpace`: Contains definition(s) of H-spaces and some basic lemmas.
- `Hopf`: Proves that the total space of the Hopf fibration is `S³`.
- `HopfConstruction`: Given a 0-connected H-space `X`, constructs a fibration `H` on `Susp A` with total space equivalent to the join `X * X`.
- `HopfJunior`: Contains `HopfJunior : S¹ → Type₀`, a fibration with fibers equivalent to `Bool` (a.k.a. the 0-sphere) and a proof that its total space is (equivalent to) `S¹`.
- `IterSuspensionStable`: Contains a reformulation of the Freudenthal suspension theorem.
- `JoinAssoc3x3`: Gives an equivalence between the joins `(A * B) * C` and `A * (B * C)`. The proof uses the 3x3-lemma.
- `JoinAssocCubical`: Gives an equivalence between the joins `(A * B) * C` and `A * (B * C)`. The proof involves squares and cubes.
- `JoinComm`: Gives an equivalence between the joins `A * B` and `B * A`.
- `JoinSusp`: Contains equivalences `Bool * A ≃ Susp A`, `Susp A * B ≃ Susp (A * B)` and `⊙Sphere m ⊙* X ⊙≃ ⊙Susp^ (S m) X` ((m+1)-fold suspension is equivalent to joining with an m-sphere).
- `LoopSpaceCircle`: Proves that the fundamental group of the circle is equivalent to the integers.
- `ModalWedgeExtension`: Lemmas about modalities and the function `X ∨ Y → X × Y` for pointed types `X` and `Y`.
- `PathSetIsInitalCover`: Proves that the covering constructed from the path set of a type `X` is initial in the category of coverings of `X`.
- `Pi2HSusp`: Given an H-space `X`, constructs an isomorphism `π₂-Susp : πS 1 (⊙Susp X) ≃ᴳ πS 0 X` between the fundamental group of `X` and the second homotopy group of its suspension.
- `PinSn`: Proves that the n-th homotopy group of the n-sphere is isomorphic to the integers.
- `PropJoinProp`: Proves that if `A` and `B` are propositions, then so is `A * B`.
- `PtdAdjoint`: Defines what a endofunctor of the category of pointed spaces is, gives two definitions of adjointness of such functors via unit and counit morphisms and via equivalence of Hom-types and constructs equivalence between the definitions. Also proves that right adjoints preserve products and left adjoints preserve wedges.
- `PtdMapSequence`: Defines data types representing sequences of pointed maps and maps between them.
- `PushoutSplit`: Shows one direction of the [pasting law for pushouts](https://ncatlab.org/nlab/show/pasting+law+for+pullbacks), namely the fact that if you compose pushout squares you get another pushout square.
- `RelativelyConstantToSetExtendsViaSurjection`: Given a surjective function `f : A → B`, a type family `C : B → Type k` of sets and a dependent function `g : (a : A) → C (f a)` such that `g` agree `g-is-const : ∀ a₁ a₂ → (p : f a₁ == f a₂) → g a₁ == g a₂ [ C ↓ p ]`, shows that there is a function `ext : (b : B) → C (f a)` such that `g` is equal to `ext ∘ f`.
- `RibbonCover`: Constructs a covering of a type `X` given a set with an action of the fundamental group of `X` on it. Used to prove an equivalence between such sets and coverings if `X` is connected in `GroupSetsRepresentCovers`.
- `SmashIsCofiber`: Proves that the smash product `Smash X Y` of two pointed types `X` and `Y` is equivalent to the cofiber of the induced map `A ∨ B → A × B`.
- `SpaceFromGroups`: Given an infinite sequence of groups, all abelian except maybe the first, constructs a type with these groups as its homotopy groups.
- `SphereEndomorphism`: Proves that the types of endomaps of a sphere and the type of basepoint-preserving such endomaps become equivalent when 0-truncated. Also proves that suspension induces an equivalence between the set of endomaps of the `n`-sphere and the set of endomaps of the `S n`-sphere for positive `n`.
- `SuspAdjointLoop`: Defines the suspension and the loop functor and proves that they are adjoint.
- `SuspAdjointLoopLadder`: Proves naturality in the covariant argument of the adjunction between the iterated suspension and the iterated loop space when phrased in terms of Hom-types.
- `SuspProduct`: Proves that `⊙Susp (X ⊙× Y) ⊙≃ ⊙Susp X ⊙∨ (⊙Susp Y ⊙∨ ⊙Susp (X ⊙∧ Y))`.
- `SuspSectionDecomp`: Let `f : X → Y` be a pointed section of `g : Y → X`. Then there is an equivalence `Susp (de⊙ Y) ≃ ⊙Susp X ∨ ⊙Susp (⊙Cofiber ⊙f)` between the suspension of `Y` and the wedge sum of the suspensions of `X` and the cofiber of `f`. This can be interpreted as a splitting in the part ΣX → ΣY → Σcofib(f) of the cofiber sequence of `f`.
- `SuspSmash`: Gives an equivalence `⊙Susp (⊙Smash X Y) ⊙≃ (X ⊙* Y)` between the suspension of the smash product and the join of two pointed types.
- `TruncationLoopLadder`: Proves the naturality of the equivalence of the 0-truncation of the m-fold loop space and the m-fold loop space of the m-truncation.
- `VanKampen`: Proves the improved version of the *Seifert–van Kampen theorem* for calculating the fundamental groupoid of a pushout from [Favonia's thesis][favonia-thesis].
- `vankampen/`: Contains definitions and lemmas for `VanKampen.agda`.
- `WedgeCofiber`: Shows that the cofiber space of `winl : X → X ∨ Y` is equivalent to `Y` and the cofiber space of `winr : Y → X ∨ Y` is equivalent to `X`.
- `WedgeExtension`: Proves the *wedge connectivity lemma* from the HoTT book (lemma 8.6.2), which basically says that given an n-connected pointed type `A` and an m-connected pointed type `B` a function `h : (w : A ∨ B) → P (∨-to-× w)`, where `P : A × B → Type` is a family of (n+m)-types, extends along `∨-to-× : A ∨ B → A × B`.

### Cohomology (directory `theorems/cohomology/`)

This directory contains proofs of interesting cohomology-theoretic theorems. Many results in this directory are described in [Evan Cavallo's thesis][ecavallo-thesis].

- `Bouquet`: Shows that the cohomology in degree n of a bouquet of n-spheres indexed by a type `I`, which has choice, is isomorphic to the product of `I` copies of `C2 0` (the 0-th cohomology of the 0-sphere) for an ordinary cohomology theory.
- `ChainComplex`: Defines the data types of (co)chain complexes and equivalences between them, defines their (co)homology groups and proves that equivalences between complex induce equivalences between their cohomology groups.
- `CoHSpace`: Contains simple lemmas about the cohomology of co-H-spaces.
- `Cogroup`: Given a type `X` with a cogroup structure and a type `Y`, proves that the map `(X ⊙→ Y) → (C n Y →ᴳ C n X)` is a group homomorphism for any cohomology theory `C`.
- `Coproduct`: Proves that `C n (X ⊙⊔ Y) ≃ᴳ C n (X ⊙∨ Y) ×ᴳ C2 n` (where `C2 n` is the `n`-th cohomology of the 0-sphere) for any cohomology theory `C`.
- `DisjointlyPointedSet`: Shows that the cohomology of a separable pointed set `X`, which has choice, is the `MinusPoint X`-fold product of `C2 0` (the 0-th cohomology of the 0-sphere) in degree 0 and trivial in higher degrees for any ordinary cohomology theory `C`.
- `EMModel`: Constructs the Eilenberg–MacLane spectrum given an abelian group and shows that its induced cohomology theory is ordinary.
- `InverseInSusp`: Shows that the homomorphism Cⁿ(ΣX) → Cⁿ(ΣX) mapping an element to its inverse is induced by a map ΣX → ΣX.
- `LongExactSequence`: Given a map `f : X → Y`, constructs the sequence Cⁿ(Y) → Cⁿ(X) → Cⁿ⁺¹(cofib(f)) → Cⁿ⁺¹(Y) → ⋯ and shows that it is exact.
- `MayerVietoris`: Given a pointed span X ←f– Z –g→ Y, shows the cofiber space of the natural map `reglue` : X ∨ Y → X ⊔\_Z Y is equivalent to the suspension of Z. Using this equivalence one can derive the Mayer–Vietoris sequence from the long exact sequence associated with `reglue`.
- `PtdMapSequence`: Functions for applying a cohomology theory to a sequence of pointed maps, producing a sequence of group homomorphisms.
- `RephraseSubFinCoboundary`: Gives a description the homomorphism induced in cohomology by a map from a bouquet of (n+1)-spheres to the suspension of a bouquet of n-spheres in terms of mapping degrees. This is used for defining cellular cohomology.
- `Sigma`: Constructs an isomorphism `C n (⊙Σ X Y) ≃ᴳ C n (⊙BigWedge Y) ×ᴳ C n X` for a type `X`, a family `Y : X → Ptd i` and any cohomology theory `C`.
- `SpectrumModel`: Shows that a spectrum induces a cohomology theory.
- `Sphere`: Shows that the cohomology of the m-sphere is `C2 0` (the 0-cohomology of the 0-sphere) in degree m and trivial in other degrees for any ordinary cohomology theory.
- `SphereEndomorphism`: Proves that the map `C n (⊙Sphere (S m)) C → n (⊙Sphere (S m))` induced by a map `f : ⊙Sphere (S m) ⊙→ ⊙Sphere (S m)` is given by multiplication with the degree of `f`.
- `SphereProduct`: Gives an isomorphism `C n (⊙Sphere m ⊙× X) ≃ᴳ C n (⊙Lift (⊙Sphere m)) ×ᴳ (C n X ×ᴳ C n (⊙Susp^ m X))` for calculating the cohomology of the product of the m-sphere and `X` for any pointed type `X` and any cohomology theory.
- `SubFinBouquet`: Constructs an explicit inverse to the function from the cohomology of the wedge of m-spheres indexed over a subfinite type `B` to the product (indexed over `B`) of the 0-th cohomology groups of the 0-sphere.
- `SubFinWedge`: Constructs an explicit inverse to the function from the cohomology of the wedge of a (sub)finite family of pointed types to the product of the cohomologies of the pointed types.
- `Theory`: Defines a data type `CohomologyTheory` of cohomology theories fulfilling some axioms similar to the Eilenberg–Steenrod axioms and proves some basic consequences of these axioms.
- `Torus`: Contains a computation of the cohomology of the n-torus.
- `Wedge`: Gives an isomorphism between Cⁿ(X ∨ Y) and Cⁿ(X) × Cⁿ(Y) (“finite additivity”) without using the additivity axiom and shows that e.g. the projection map to Cⁿ(X) is induced by the inclusion of X in X ∨ Y and similarly for other maps.

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
    and Eric Finster
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
- Eric Finster: modalities
- Jesper Cockx: rewrite rules
- Christian Sattler: updates to equivalence and univalence
- Chris Jeris: Eckmann-Hilton argument
- Michael Shulman: updates to equivalence and univalence

License
-------
This work is released under [MIT license](https://opensource.org/licenses/MIT).
See [LICENSE.md](LICENSE.md).

Acknowledgments
---------------

This material was sponsored by the National Science Foundation under grant number CCF-1116703;
Air Force Office of Scientific Research under grant numbers FA-95501210370 and FA-95501510053.
The views and conclusions contained in this document are those of the author and should not be
interpreted as representing the official policies, either expressed or implied, of any sponsoring
institution, the U.S. government or any other entity.

[favonia-thesis]: http://favonia.org/thesis.html
[guillaume-brunerie-thesis]: https://arxiv.org/abs/1606.05916
[ecavallo-thesis]: http://www.cs.cmu.edu/~ecavallo/works/thesis.pdf