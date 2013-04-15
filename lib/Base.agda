{-# OPTIONS --without-K #-}

module lib.Base where

-- Universe levels

postulate  -- Universe levels
  ULevel : Set
  zero : ULevel
  suc : ULevel → ULevel
  max : ULevel → ULevel → ULevel

{-# BUILTIN LEVEL ULevel #-}
{-# BUILTIN LEVELZERO zero #-}
{-# BUILTIN LEVELSUC suc #-}
{-# BUILTIN LEVELMAX max #-}


-- Universes

Type : (i : ULevel) → Set (suc i)
Type i = Set i

Type₀ = Set₀
Type0 = Set0

Type₁ = Set₁
Type1 = Set1


-- Identity type
infixr 4 _==_

data _==_ {i} {A : Type i} (a : A) : A → Type i where
  idp : a == a

Path = _==_

-- -- This should not be provable
-- K : {A : Type₀} → (x : A) → (p : x == x) → p == idp
-- K x p = {!p!}


-- Path over a path

PathOver : ∀ {i j} {A : Type i} (B : A → Type j)
  {x y : A} (p : x == y) (u : B x) (v : B y) → Type j
PathOver B idp u v = (u == v)

syntax PathOver B p u v =
  u == v [ B ↓ p ]

ap : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y : A}
  → (x == y → f x == f y)
ap f idp = idp

apd : ∀ {i j} {A : Type i} {B : A → Type j} (f : (a : A) → B a) {x y : A}
  → (p : x == y) → f x == f y [ B ↓ p ]
apd f idp = idp

transport : ∀ {i j} {A : Type i} (B : A → Type j) {x y : A} (p : x == y)
  → (B x → B y)
transport B idp t = t

-- Make equational reasoning more readable
syntax ap f p = p |in-ctx f


Π : ∀ {i j} (A : Type i) (P : A → Type j) → Type (max i j)
Π A P = (x : A) → P x

record Σ {i j} (A : Type i) (B : A → Type j) : Type (max i j) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

data ⊥ {i} : Type i where  -- \bot

¬ : ∀ {i} (A : Type i) → Type i
¬ {i} A = A → ⊥ {i}

⊥-rec : ∀ {i j} {A : Type j} → (⊥ {i} → A)
⊥-rec ()

_=/=_ : ∀ {i} {A : Type i} → (A → A → Type i)
x =/= y = ¬ (x == y)

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
