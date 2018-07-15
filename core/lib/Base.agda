{-# OPTIONS --without-K --rewriting #-}

{-
This file contains a bunch of basic stuff which is needed early.
Maybe it should be organised better.
-}

module lib.Base where

{- Universes and typing

Agda has explicit universe polymorphism, which means that there is an actual
type of universe levels on which you can quantify. This type is called [ULevel]
and comes equipped with the following operations:

- [lzero] : [ULevel] (in order to have at least one universe)
- [lsucc] : [ULevel → ULevel] (the [i]th universe level is a term in the
  [lsucc i]th universe)
- [lmax] : [ULevel → ULevel → ULevel] (in order to type dependent products (where
  the codomain is in a uniform universe level)

This type is postulated below and linked to Agda’s universe polymorphism
mechanism via the built-in module Agda.Primitive (it’s the new way).

In plain Agda, the [i]th universe is called [Set i], which is not a very good
name from the point of view of HoTT, so we define [Type] as a synonym of [Set]
and [Set] should never be used again.
-}

open import Agda.Primitive public using (lzero)
  renaming (Level to ULevel; lsuc to lsucc; _⊔_ to lmax)

Type : (i : ULevel) → Set (lsucc i)
Type i = Set i

Type₀ = Type lzero
Type0 = Type lzero

Type₁ = Type (lsucc lzero)
Type1 = Type (lsucc lzero)

{-
There is no built-in or standard way to coerce an ambiguous term to a given type
(like [u : A] in ML), the symbol [:] is reserved, and the Unicode [∶] is really
a bad idea.
So we’re using the symbol [_:>_], which has the advantage that it can micmic
Coq’s [u = v :> A].
-}

of-type : ∀ {i} (A : Type i) (u : A) → A
of-type A u = u

infix 40 of-type
syntax of-type A u =  u :> A

{- Instance search -}

⟨⟩ : ∀ {i} {A : Type i} {{a : A}} → A
⟨⟩ {{a}} = a

{- Identity type

The identity type is called [Path] and [_==_] because the symbol [=] is
reserved in Agda.
The constant path is [idp]. Note that all arguments of [idp] are implicit.
-}

infix 30 _==_
data _==_ {i} {A : Type i} (a : A) : A → Type i where
  idp : a == a

Path = _==_

{-# BUILTIN EQUALITY _==_ #-}

{- Paulin-Mohring J rule

At the time I’m writing this (July 2013), the identity type is somehow broken in
Agda dev, it behaves more or less as the Martin-Löf identity type instead of
behaving like the Paulin-Mohring identity type.
So here is the Paulin-Mohring J rule -}

J : ∀ {i j} {A : Type i} {a : A} (B : (a' : A) (p : a == a') → Type j) (d : B a idp)
  {a' : A} (p : a == a') → B a' p
J B d idp = d

J' : ∀ {i j} {A : Type i} {a : A} (B : (a' : A) (p : a' == a) → Type j) (d : B a idp)
  {a' : A} (p : a' == a) → B a' p
J' B d idp = d

infixr 80 _∙_

_∙_ : ∀ {i} {A : Type i} {x y z : A}
  → (x == y → y == z → x == z)
idp ∙ q = q

{- Rewriting

This is a new pragma added to Agda to help create higher inductive types.
-}

infix 30 _↦_
postulate  -- HIT
  _↦_ : ∀ {i} {A : Type i} → A → A → Type i

{-# BUILTIN REWRITE _↦_ #-}

{- Unit type

The unit type is defined as record so that we also get the η-rule definitionally.
-}

record ⊤ : Type₀ where
  instance constructor unit

Unit = ⊤

{-# BUILTIN UNIT ⊤ #-}


{- Dependent paths

The notion of dependent path is a very important notion.
If you have a dependent type [B] over [A], a path [p : x == y] in [A] and two
points [u : B x] and [v : B y], there is a type [u == v [ B ↓ p ]] of paths from
[u] to [v] lying over the path [p].
By definition, if [p] is a constant path, then [u == v [ B ↓ p ]] is just an
ordinary path in the fiber.
-}

PathOver : ∀ {i j} {A : Type i} (B : A → Type j)
  {x y : A} (p : x == y) (u : B x) (v : B y) → Type j
PathOver B idp u v = (u == v)

infix 30 PathOver
syntax PathOver B p u v =
  u == v [ B ↓ p ]

{- Ap, coe and transport

Given two fibrations over a type [A], a fiberwise map between the two fibrations
can be applied to any dependent path in the first fibration ([ap↓]).
As a special case, when [A] is [Unit], we find the familiar [ap] ([ap] is
defined in terms of [ap↓] because it shouldn’t change anything for the user
and this is helpful in some rare cases)
-}

ap : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y : A}
  → (x == y → f x == f y)
ap f idp = idp

ap↓ : ∀ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k}
  (g : {a : A} → B a → C a) {x y : A} {p : x == y}
  {u : B x} {v : B y}
  → (u == v [ B ↓ p ] → g u == g v [ C ↓ p ])
ap↓ g {p = idp} p = ap g p

{-
[apd↓] is defined in lib.PathOver. Unlike [ap↓] and [ap], [apd] is not
definitionally a special case of [apd↓]
-}

apd : ∀ {i j} {A : Type i} {B : A → Type j} (f : (a : A) → B a) {x y : A}
  → (p : x == y) → f x == f y [ B ↓ p ]
apd f idp = idp

{-
An equality between types gives two maps back and forth
-}

coe : ∀ {i} {A B : Type i} (p : A == B) → A → B
coe idp x = x

coe! : ∀ {i} {A B : Type i} (p : A == B) → B → A
coe! idp x = x

{-
The operations of transport forward and backward are defined in terms of [ap]
and [coe], because this is more convenient in practice.
-}

transport : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x == y)
  → (B x → B y)
transport B p = coe (ap B p)

transport! : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x == y)
  → (B y → B x)
transport! B p = coe! (ap B p)

{- Π-types

Shorter notation for Π-types.
-}

Π : ∀ {i j} (A : Type i) (P : A → Type j) → Type (lmax i j)
Π A P = (x : A) → P x


{- Σ-types

Σ-types are defined as a record so that we have definitional η.
-}

infixr 60 _,_

record Σ {i j} (A : Type i) (B : A → Type j) : Type (lmax i j) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

pair= : ∀ {i j} {A : Type i} {B : A → Type j}
  {a a' : A} (p : a == a') {b : B a} {b' : B a'}
  (q : b == b' [ B ↓ p ])
  → (a , b) == (a' , b')
pair= idp q = ap (_ ,_) q

pair×= : ∀ {i j} {A : Type i} {B : Type j}
  {a a' : A} (p : a == a') {b b' : B} (q : b == b')
  → (a , b) == (a' , b')
pair×= idp q = pair= idp q


{- Empty type

We define the eliminator of the empty type using an absurd pattern. Given that
absurd patterns are not consistent with HIT, we will not use empty patterns
anymore after that.
-}

data ⊥ : Type₀ where

Empty = ⊥

⊥-elim : ∀ {i} {P : ⊥ → Type i} → ((x : ⊥) → P x)
⊥-elim ()

Empty-elim = ⊥-elim

{- Negation and disequality -}

¬ : ∀ {i} (A : Type i) → Type i
¬ A = A → ⊥

_≠_ : ∀ {i} {A : Type i} → (A → A → Type i)
x ≠ y = ¬ (x == y)


{- Natural numbers -}

data ℕ : Type₀ where
  O : ℕ
  S : (n : ℕ) → ℕ

Nat = ℕ

{-# BUILTIN NATURAL ℕ #-}


{- Lifting to a higher universe level

The operation of lifting enjoys both β and η definitionally.
It’s a bit annoying to use, but it’s not used much (for now).
-}

record Lift {i j} (A : Type i) : Type (lmax i j) where
  instance constructor lift
  field
    lower : A
open Lift public


{- Equational reasoning

Equational reasoning is a way to write readable chains of equalities.
The idea is that you can write the following:

  t : a == e
  t = a =⟨ p ⟩
      b =⟨ q ⟩
      c =⟨ r ⟩
      d =⟨ s ⟩
      e ∎

where [p] is a path from [a] to [b], [q] is a path from [b] to [c], and so on.

You often have to apply some equality in some context, for instance [p] could be
[ap ctx thm] where [thm] is the interesting theorem used to prove that [a] is
equal to [b], and [ctx] is the context.
In such cases, you can use instead [thm |in-ctx ctx]. The advantage is that
[ctx] is usually boring whereas the first word of [thm] is the most interesting
part.

_=⟨_⟩ is not definitionally the same thing as concatenation of paths _∙_ because
we haven’t defined concatenation of paths yet, and also you probably shouldn’t
reason on paths constructed with equational reasoning.
If you do want to reason on paths constructed with equational reasoning, check
out PathSeq (below) instead.
-}

infixr 10 _=⟨_⟩_
infix  15 _=∎

_=⟨_⟩_ : ∀ {i} {A : Type i} (x : A) {y z : A} → x == y → y == z → x == z
_ =⟨ idp ⟩ idp = idp

_=∎ : ∀ {i} {A : Type i} (x : A) → x == x
_ =∎ = idp

infixl 40 ap
syntax ap f p = p |in-ctx f

{- Path sequences

Path sequences reify concatenations of paths and thereby enable
manipulations of such sequences. They provide an alternative to
equational reasoning with _=⟨_⟩_:

When you write the following (with the usual equational reasoning combinators):

  t : a == e
  t = a =⟨ p ⟩
      b =⟨ q ⟩
      c =⟨ r ⟩
      d =⟨ s ⟩
      e ∎

it just creates the concatenation of [p], [q], [r] and [s] and there is no way
to say “remove the last step to get the path from [a] to [d]”.
With path sequences you would write:

  t : PathSeq a e
  t = a =⟪ p ⟫
      b =⟪ q ⟫
      c =⟪ r ⟫
      d =⟪ s ⟫
      e ∎∎

Then the actual path from [a] to [e] is [↯ t], and you can strip any number
of steps from the beginning or the end:

  ↯ t !2

(The function [_!2] is defined in `lib.PathSeq`.)

There is also support for reasoning about path sequences.
For example, you may want to construct a path between the path [p ∙ q ∙ r ∙ s]
constructed above and [p ∙ r' ∙ q' ∙ s] by using a path [u : q ∙ r == r' ∙ q'].
Without path sequences, you would do this like this:

  ex : p ∙ q ∙ r ∙ s == p ∙ r' ∙ q' ∙ s
  ex =
    p ∙ q ∙ r ∙ s
      =⟨ ap (p ∙_) (! (∙-assoc q r s))
    p ∙ (q ∙ r) ∙ s
      =⟨ ap (λ v → p ∙ v ∙ s) u ⟩
    p ∙ (r' ∙ q') ∙ s
      =⟨ ap (p ∙_) (∙-assoc r' q' s) ⟩
    p ∙ r' ∙ q' ∙ s =∎

With path sequences this can be simplified as follows
(given [u : q ◃∙ r ◃∎ =ₛ r' ◃∙ q' ◃∎]):

  ex' : p ◃∙ q ◃∙ r ◃∙ s ◃∎ =ₛ p ◃∙ r' ◃∙ q' ◃∙ s ◃∎
  ex' =
    p ◃∙ q ◃∙ r ◃∙ s ◃∎
      =ₛ⟨ 1 & 2 & u ⟩
    p ◃∙ r' ◃∙ q' ◃∙ s ◃∎ ∎ₛ

In this example, 1 is the position where to start rewriting (that is, between [p] and [q])
and 2 is the number of subpaths to replace (namely, [q] and [r]).
-}

module _ {i} {A : Type i} where
  infixr 80 _◃∙_
  data PathSeq : A → A → Type i where
    [] : {a : A} → PathSeq a a
    _◃∙_ : {a a' a'' : A} (p : a == a') (s : PathSeq a' a'') → PathSeq a a''

  infix 30 _=-=_
  _=-=_ = PathSeq

  infix 90 _◃∎
  _◃∎ : {a a' : A} → a == a' → a =-= a'
  _◃∎ {a} {a'} p = p ◃∙ []

  infix 15 _∎∎
  infixr 10 _=⟪_⟫_
  infixr 10 _=⟪idp⟫_

  _∎∎ : (a : A) → a =-= a
  _∎∎ _ = []

  _=⟪_⟫_ : (a : A) {a' a'' : A} (p : a == a') (s : a' =-= a'') → a =-= a''
  _=⟪_⟫_ _ p s = p ◃∙ s

  _=⟪idp⟫_ : (a : A) {a' : A} (s : a =-= a') → a =-= a'
  a =⟪idp⟫ s = s

  ↯ : {a a' : A} (s : a =-= a') → a == a'
  ↯ [] = idp
  ↯ (p ◃∙ []) = p
  ↯ (p ◃∙ s@(_ ◃∙ _)) = p ∙ ↯ s

  {- 'ₛ' is for sequence -}
  record _=ₛ_ {a a' : A} (s t : a =-= a') : Type i where
    constructor =ₛ-in
    field
      =ₛ-out : ↯ s == ↯ t

  open _=ₛ_ public

{- Various basic functions and function operations

The identity function on a type [A] is [idf A] and the constant function at some
point [b] is [cst b].

Composition of functions ([_∘_]) can handle dependent functions.
-}

idf : ∀ {i} (A : Type i) → (A → A)
idf A = λ x → x

cst : ∀ {i j} {A : Type i} {B : Type j} (b : B) → (A → B)
cst b = λ _ → b

infixr 80 _∘_

_∘_ : ∀ {i j k} {A : Type i} {B : A → Type j} {C : (a : A) → (B a → Type k)}
  → (g : {a : A} → Π (B a) (C a)) → (f : Π A B) → Π A (λ a → C a (f a))
g ∘ f = λ x → g (f x)

-- Application
infixr 0 _$_
_$_ : ∀ {i j} {A : Type i} {B : A → Type j} → (∀ x → B x) → (∀ x → B x)
f $ x = f x

-- (Un)curryfication
curry : ∀ {i j k} {A : Type i} {B : A → Type j} {C : Σ A B → Type k}
  → (∀ s → C s) → (∀ x y → C (x , y))
curry f x y = f (x , y)

uncurry : ∀ {i j k} {A : Type i} {B : A → Type j} {C : ∀ x → B x → Type k}
  → (∀ x y → C x y) → (∀ s → C (fst s) (snd s))
uncurry f (x , y) = f x y

{- Truncation levels

The type of truncation levels is isomorphic to the type of natural numbers but
"starts at -2".
-}

data TLevel : Type₀ where
  ⟨-2⟩ : TLevel
  S : (n : TLevel) → TLevel

ℕ₋₂ = TLevel

⟨_⟩₋₂ : ℕ → ℕ₋₂
⟨ O ⟩₋₂ = ⟨-2⟩
⟨ S n ⟩₋₂ = S ⟨ n ⟩₋₂

{- Coproducts and case analysis -}

data Coprod {i j} (A : Type i) (B : Type j) : Type (lmax i j) where
  inl : A → Coprod A B
  inr : B → Coprod A B

infixr 80 _⊔_
_⊔_ = Coprod

Dec : ∀ {i} (P : Type i) → Type i
Dec P = P ⊔ ¬ P

{-
Pointed types and pointed maps.

[A ⊙→ B] was pointed, but it was never used as a pointed type.
-}

infix 60 ⊙[_,_]

record Ptd (i : ULevel) : Type (lsucc i) where
  constructor ⊙[_,_]
  field
    de⊙ : Type i
    pt : de⊙
open Ptd public

ptd : ∀ {i} (A : Type i) → A → Ptd i
ptd = ⊙[_,_]

ptd= : ∀ {i} {A A' : Type i} (p : A == A')
  {a : A} {a' : A'} (q : a == a' [ idf _ ↓ p ])
  → ⊙[ A , a ] == ⊙[ A' , a' ]
ptd= idp q = ap ⊙[ _ ,_] q

Ptd₀ = Ptd lzero

infixr 0 _⊙→_
_⊙→_ : ∀ {i j} → Ptd i → Ptd j → Type (lmax i j)
⊙[ A , a₀ ] ⊙→ ⊙[ B , b₀ ] = Σ (A → B) (λ f → f a₀ == b₀)

⊙idf : ∀ {i} (X : Ptd i) → X ⊙→ X
⊙idf X = (λ x → x) , idp

⊙cst : ∀ {i j} {X : Ptd i} {Y : Ptd j} → X ⊙→ Y
⊙cst {Y = Y} = (λ x → pt Y) , idp


{-
Used in a hack to make HITs maybe consistent. This is just a parametrized unit
type (positively)
-}

data Phantom {i} {A : Type i} (a : A) : Type₀ where
  phantom : Phantom a

{-
Numeric literal overloading

This enables writing numeric literals
-}

record FromNat {i} (A : Type i) : Type (lsucc i) where
  field
    in-range : ℕ → Type i
    read : ∀ n → ⦃ _ : in-range n ⦄ → A

open FromNat ⦃...⦄ public using () renaming (read to from-nat)

{-# BUILTIN FROMNAT from-nat #-}

record FromNeg {i} (A : Type i) : Type (lsucc i) where
  field
    in-range : ℕ → Type i
    read : ∀ n → ⦃ _ : in-range n ⦄ → A

open FromNeg ⦃...⦄ public using () renaming (read to from-neg)

{-# BUILTIN FROMNEG from-neg #-}

instance
  ℕ-reader : FromNat ℕ
  FromNat.in-range ℕ-reader _ = ⊤
  FromNat.read ℕ-reader n = n

  TLevel-reader : FromNat TLevel
  FromNat.in-range TLevel-reader _ = ⊤
  FromNat.read TLevel-reader n = S (S ⟨ n ⟩₋₂)

  TLevel-neg-reader : FromNeg TLevel
  FromNeg.in-range TLevel-neg-reader O = ⊤
  FromNeg.in-range TLevel-neg-reader 1 = ⊤
  FromNeg.in-range TLevel-neg-reader 2 = ⊤
  FromNeg.in-range TLevel-neg-reader (S (S (S _))) = ⊥
  FromNeg.read TLevel-neg-reader O = S (S ⟨-2⟩)
  FromNeg.read TLevel-neg-reader 1 = S ⟨-2⟩
  FromNeg.read TLevel-neg-reader 2 = ⟨-2⟩
  FromNeg.read TLevel-neg-reader (S (S (S _))) ⦃()⦄
