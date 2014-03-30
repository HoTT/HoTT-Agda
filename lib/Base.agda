{-# OPTIONS --without-K #-}

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
mechanism via the BUILTIN commands (it’s the way it works).

In plain Agda, the [i]th universe is called [Set i], which is not a very good
name from the point of view of HoTT, so we define [Type] as a synonym of [Set]
and [Set] should never be used again.
-}

postulate  -- Universe levels
  ULevel : Set
  lzero : ULevel
  lsucc : ULevel → ULevel
  lmax : ULevel → ULevel → ULevel

{-# BUILTIN LEVEL ULevel #-}
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC lsucc #-}
{-# BUILTIN LEVELMAX lmax #-}

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

infix 10 of-type

of-type : ∀ {i} (A : Type i) (u : A) → A
of-type A u = u

syntax of-type A u =  u :> A

{- Identity type

The identity type is called [Path] and [_==_] because the symbol [=] is
reserved in Agda.
The constant path is [idp]. Note that all arguments of [idp] are implicit.
-}

infix 3 _==_

data _==_ {i} {A : Type i} (a : A) : A → Type i where
  idp : a == a

Path = _==_

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL  idp #-}

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

{- Unit type

The unit type is defined as record so that we also get the η-rule definitionally.
-}

record Unit : Type₀ where
  constructor unit

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

infixr 1 _,_

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
pair= idp q = ap (_,_ _) q

pair×= : ∀ {i j} {A : Type i} {B : Type j}
  {a a' : A} (p : a == a') {b b' : B} (q : b == b')
  → (a , b) == (a' , b')
pair×= idp q = pair= idp q


{- Empty type

We define the eliminator of the empty type using an absurd pattern. Given that
absurd patterns are not consistent with HIT, we will not use empty patterns
anymore after that.
-}

data Empty : Type₀ where

Empty-elim : ∀ {i} {P : Empty → Type i} → ((x : Empty) → P x)
Empty-elim ()


{- Negation and disequality -}

¬ : ∀ {i} (A : Type i) → Type i
¬ A = A → Empty

_≠_ : ∀ {i} {A : Type i} → (A → A → Type i)
x ≠ y = ¬ (x == y)


{- Lifting to a higher universe level

The operation of lifting enjoys both β and η definitionally.
It’s a bit annoying to use, but it’s not used much (for now).
-}

record Lift {i j} (A : Type i) : Type (lmax i j) where
  constructor lift
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
out lib.types.PathSeq instead.
-}

infix  2 _∎
infixr 2 _=⟨_⟩_

_=⟨_⟩_ : ∀ {i} {A : Type i} (x : A) {y z : A} → x == y → y == z → x == z
_ =⟨ idp ⟩ idp = idp

_∎ : ∀ {i} {A : Type i} (x : A) → x == x
_ ∎ = idp

syntax ap f p = p |in-ctx f

{- Various basic functions and function operations

The identity function on a type [A] is [idf A] and the constant function at some
point [b] is [cst b].

Composition of functions ([_∘_]) can handle dependent functions.
-}

idf : ∀ {i} (A : Type i) → (A → A)
idf A = λ x → x

cst : ∀ {i j} {A : Type i} {B : Type j} (b : B) → (A → B)
cst b = λ _ → b

infixr 4 _∘_

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

-- (Un)curryfication with the first argument made implicit
curryi : ∀ {i j k} {A : Type i} {B : A → Type j} {C : Σ A B → Type k}
  → (∀ s → C s) → (∀ {x} y → C (x , y))
curryi f y = f (_ , y)

uncurryi : ∀ {i j k} {A : Type i} {B : A → Type j} {C : ∀ x → B x → Type k}
  → (∀ {x} y → C x y) → (∀ s → C (fst s) (snd s))
uncurryi f (x , y) = f y

{- Truncation levels

The type of truncation levels is isomorphic to the type of natural numbers but
"starts at -2".
-}

data TLevel : Type₀ where
  ⟨-2⟩ : TLevel
  S : (n : TLevel) → TLevel

ℕ₋₂ = TLevel

⟨-1⟩ : TLevel
⟨-1⟩ = S ⟨-2⟩

⟨0⟩ : TLevel
⟨0⟩ = S ⟨-1⟩

{- Coproducts and case analysis -}

data Coprod {i j} (A : Type i) (B : Type j) : Type (lmax i j) where
  inl : A → Coprod A B
  inr : B → Coprod A B

match_withl_withr_ : ∀ {i j k} {A : Type i} {B : Type j}
  {C : Coprod A B → Type k}
  (x : Coprod A B) (l : (a : A) → C (inl a)) (r : (b : B) → C (inr b)) → C x
match (inl a) withl l withr r = l a
match (inr b) withl l withr r = r b

{-
Used in a hack to make HITs maybe consistent. This is just a parametrized unit
type (positively)
-}

data Phantom {i} {A : Type i} (a : A) : Type₀ where
  phantom : Phantom a

{-
-- When you want to cheat

module ADMIT where
  postulate
    ADMIT : ∀ {i} {A : Type i} → A
-}
