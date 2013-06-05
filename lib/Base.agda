{-# OPTIONS --without-K #-}

module lib.Base where

{- Universe and typing -}

postulate  -- Universe levels
  ULevel : Set  -- [Set] is allowed here
  zero : ULevel
  suc : ULevel → ULevel
  max : ULevel → ULevel → ULevel

{-# BUILTIN LEVEL ULevel #-}
{-# BUILTIN LEVELZERO zero #-}
{-# BUILTIN LEVELSUC suc #-}
{-# BUILTIN LEVELMAX max #-}

Type : (i : ULevel) → Set (suc i)  -- [Set] is allowed here
Type i = Set i  -- [Set] is allowed here

Type₀ = Type zero
Type0 = Type zero

Type₁ = Type (suc zero)
Type1 = Type (suc zero)

infix 10 of-type

of-type : ∀ {i} (A : Type i) (u : A) → A
of-type A u = u

syntax of-type A u =  u :> A

{- Identity type -}

infix 4 _==_

data _==_ {i} {A : Type i} (a : A) : A → Type i where
  idp : a == a

Path = _==_

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL  idp #-}

-- -- This should not be provable
-- K : {A : Type₀} {x : A} (p : x == x) → p == idp
-- K idp = idp


record ⊤ : Type₀ where
  constructor tt


{- Dependent paths -}

PathOver : ∀ {i j} {A : Type i} (B : A → Type j)
  {x y : A} (p : x == y) (u : B x) (v : B y) → Type j
PathOver B idp u v = (u == v)

syntax PathOver B p u v =
  u == v [ B ↓ p ]

-- This is the most general non-dependent version of [ap].
-- The usual [ap] is deduced from it.
ap↓ : ∀ {i j k} {A : Set i} {B : A → Set j} {C : A → Set k}
  (g : {a : A} → B a → C a) {x y : A} {p : x == y}
  {u : B x} {v : B y} (q : u == v [ B ↓ p ])
  → g u == g v [ C ↓ p ]
ap↓ g {p = idp} idp = idp

ap : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y : A}
  → (x == y → f x == f y)
ap f p = ap↓ {A = ⊤} f {p = idp} p

apd : ∀ {i j} {A : Type i} {B : A → Type j} (f : (a : A) → B a) {x y : A}
  → (p : x == y) → f x == f y [ B ↓ p ]
apd f idp = idp

coe : ∀ {i} {A B : Type i} (p : A == B) → A → B
coe idp x = x

coe! : ∀ {i} {A B : Type i} (p : A == B) → B → A
coe! idp x = x

transport : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x == y)
  → (B x → B y)
transport B p = coe (ap B p)

transport! : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x == y)
  → (B y → B x)
transport! B p = coe! (ap B p)

-- Make equational reasoning more readable
syntax ap f p = p |in-ctx f


-- Π-types

Π : ∀ {i j} (A : Type i) (P : A → Type j) → Type (max i j)
Π A P = (x : A) → P x


-- Σ-types

record Σ {i j} (A : Type i) (B : A → Type j) : Type (max i j) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public


-- Empty type

data ⊥ : Type₀ where  -- \bot

⊥-rec : ∀ {i} {A : Type i} → (⊥ → A)
⊥-rec ()  -- This empty pattern is allowed


-- Negation

¬ : ∀ {i} (A : Type i) → Type i
¬ A = A → ⊥

_≠_ : ∀ {i} {A : Type i} → (A → A → Type i)
x ≠ y = ¬ (x == y)


-- Lifting

record Lift {i j} (A : Type i) : Type (max i j) where
  constructor lift
  field
    lower : A
open Lift public

infixr 8 _∙_

_∙_ : ∀ {i} {A : Type i} {x y z : A}
  → (x == y → y == z → x == z)
idp ∙ q = q

! : ∀ {i} {A : Type i} {x y : A}
  → (x == y → y == x)
! idp = idp

-- Equational reasoning combinator

infix  2 _∎
infixr 2 _=⟨_⟩_

_=⟨_⟩_ : ∀ {i} {A : Type i} (x : A) {y z : A} → x == y → y == z → x == z
_ =⟨ p ⟩ q = p ∙ q

_∎ : ∀ {i} {A : Type i} (x : A) → x == x
_ ∎ = idp

-- Identity functions
idf : ∀ {i} (A : Type i) → (A → A)
idf A = λ x → x

-- Constant functions
cst : ∀ {i j} {A : Type i} {B : Type j} (b : B) → (A → B)
cst b = λ _ → b

infixr 2 _∘_

-- Composition of dependent functions
_∘_ : ∀ {i j k} {A : Type i} {B : A → Type j} {C : (a : A) → (B a → Type k)}
  → (g : {a : A} → Π (B a) (C a)) → (f : Π A B) → Π A (λ a → C a (f a))
g ∘ f = λ x → g (f x)

-- Application
infixr 0 _$_
_$_ : ∀ {i j} {A : Type i} {B : A → Type j} → (∀ x → B x) → (∀ x → B x)
f $ x = f x


data ℕ₋₂ : Type₀ where
  ⟨-2⟩ : ℕ₋₂
  S : (n : ℕ₋₂) → ℕ₋₂

⟨-1⟩ : ℕ₋₂
⟨-1⟩ = S ⟨-2⟩

⟨0⟩ : ℕ₋₂
⟨0⟩ = S ⟨-1⟩

data Coprod {i j} (A : Type i) (B : Type j) : Type (max i j) where
  inl : A → Coprod A B
  inr : B → Coprod A B

match_withl_withr_ : ∀ {i j k} {A : Type i} {B : Type j}
  {C : Coprod A B → Type k}
  (x : Coprod A B) (l : (a : A) → C (inl a)) (r : (b : B) → C (inr b)) → C x
match (inl a) withl l withr r = l a
match (inr b) withl l withr r = r b



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

pair= : ∀ {i j} {A : Type i} {B : A → Type j}
  {a a' : A} (p : a == a') {b : B a} {b' : B a'}
  (q : b == b' [ B ↓ p ])
  → (a , b) == (a' , b')
pair= idp idp = idp

pair=' : ∀ {i j} {A : Type i} {B : Type j}
  {a a' : A} (p : a == a') {b b' : B} (q : b == b')
  → (a , b) == (a' , b')
pair=' idp q = pair= idp q


-- When you want to cheat

module ADMIT where
  postulate
    ADMIT : ∀ {i} {A : Type i} → A
