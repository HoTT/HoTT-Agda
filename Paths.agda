{-# OPTIONS --without-K #-}

open import Types
open import Functions

module Paths where

-- Identity type
infix 4 _≡_  -- \equiv

data _≡_ {i} {A : Set i} : A → A → Set i where
  refl : (a : A) → a ≡ a

_≢_ : ∀ {i} {A : Set i} → (A → A → Set i)
x ≢ y = ¬ (x ≡ y)

-- -- This should not be provable
-- K : {A : Set} → (x : A) → (p : x ≡ x) → p ≡ refl x
-- K .x (refl x) = refl _

-- Composition and opposite of paths

infix 8 _∘_  -- \o

_∘_ : ∀ {i} {A : Set i} {x y z : A} → (x ≡ y → y ≡ z → x ≡ z)
refl _ ∘ q = q

! : ∀ {i} {A : Set i} {x y : A} → (x ≡ y → y ≡ x)
! (refl _) = refl _

-- Equational reasioning combinator
-- (from Nils' library)

infix  0 finally
infixr 0 _≡⟨_⟩_

_≡⟨_⟩_ : ∀ {ℓ} {A : Set ℓ} x {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = x≡y ∘ y≡z

finally : ∀ {ℓ} {A : Set ℓ} (x y : A) → x ≡ y → x ≡ y
finally _ _ x≡y = x≡y

syntax finally x y x≡y = x ≡⟨ x≡y ⟩∎ y ∎

-- Transport and map

transport : ∀ {i j} {A : Set i} (P : A → Set j) {x y : A}
  → (x ≡ y → P x → P y)
transport P (refl _) t = t

map : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) {x y : A}
  → (x ≡ y → f x ≡ f y)
map f (refl _) = refl _

map-dep : ∀ {i j} {A : Set i} {P : A → Set j} (f : (a : A) → P a) {x y : A}
  → (p : x ≡ y) → transport P p (f x) ≡ f y
map-dep f (refl _) = refl _

map-dep! : ∀ {i j} {A : Set i} {P : A → Set j} (f : (a : A) → P a) {x y : A}
  → (p : x ≡ y) → f x ≡ transport P (! p) (f y)
map-dep! f (refl _) = refl _

-- Alternative names for map

ap : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) {x y : A}
  → (x ≡ y → f x ≡ f y)
ap = map

apd : ∀ {i j} {A : Set i} {P : A → Set j} (f : (a : A) → P a) {x y : A}
  → (p : x ≡ y) → transport P p (f x) ≡ f y
apd = map-dep

apd! : ∀ {i j} {A : Set i} {P : A → Set j} (f : (a : A) → P a) {x y : A}
  → (p : x ≡ y) → f x ≡ transport P (! p) (f y)
apd! = map-dep!

-- Paths in Sigma types

module _ {i j} {A : Set i} {P : A → Set j} where

  ap2 : ∀ {k} {Q : Set k} (f : (a : A) → P a → Q)
    {x y : A} (p : x ≡ y) {u : P x} {v : P y}
    (q : transport P p u ≡ v) → f x u ≡ f y v
  ap2 f (refl _) (refl _) = refl _

  Σ-eq : {x y : A} (p : x ≡ y) {u : P x} {v : P y}
    (q : transport P p u ≡ v) → (x , u) ≡ (y , v)
  Σ-eq = ap2 _,_

  -- Same as [Σ-eq] but with only one argument
  total-Σ-eq : {xu yv : Σ A P}
    (q : Σ (π₁ xu ≡ π₁ yv) (λ p → transport P p (π₂ xu) ≡ (π₂ yv)))
    → xu ≡ yv
  total-Σ-eq (p , q) = Σ-eq p q

  base-path : {x y : Σ A P} (p : x ≡ y) → π₁ x ≡ π₁ y
  base-path = map π₁

  trans-base-path : {x y : Σ A P} (p : x ≡ y)
    → transport P (base-path p) (π₂ x) ≡ π₂ y
  trans-base-path {_} {._} (refl ._) = refl _

  fiber-path : {x y : Σ A P} (p : x ≡ y)
    → transport P (base-path p) (π₂ x) ≡ π₂ y
  fiber-path {x} {.x} (refl .x) = refl _

  abstract
    base-path-Σ-eq : {x y : A} (p : x ≡ y) {u : P x} {v : P y}
      (q : transport P p u ≡ v) → base-path (Σ-eq p q) ≡ p
    base-path-Σ-eq (refl _) (refl _) = refl _

    fiber-path-Σ-eq : {x y : A} (p : x ≡ y) {u : P x} {v : P y}
      (q : transport P p u ≡ v)
      → transport (λ t → transport P t u ≡ v) (base-path-Σ-eq p q)
                  (fiber-path (Σ-eq p q))
        ≡ q
    fiber-path-Σ-eq (refl _) (refl _) = refl _

    Σ-eq-base-path-fiber-path : {x y : Σ A P} (p : x ≡ y)
      → Σ-eq (base-path p) (fiber-path p) ≡ p
    Σ-eq-base-path-fiber-path {x} {.x} (refl .x) = refl _

-- Some of the ∞-groupoid structure

module _ {i} {A : Set i} where

  concat-assoc : {x y z t : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ t)
    → (p ∘ q) ∘ r ≡ p ∘ (q ∘ r)
  concat-assoc (refl _) _ _ = refl _

  -- [refl-left-unit] is definitionally true

  refl-right-unit : {x y : A} (q : x ≡ y) → q ∘ refl _ ≡ q
  refl-right-unit (refl _) = refl _

  opposite-left-inverse : {x y : A} (p : x ≡ y) → (! p) ∘ p ≡ refl _
  opposite-left-inverse (refl _) = refl _

  opposite-right-inverse : {x y : A} (p : x ≡ y) → p ∘ (! p) ≡ refl _
  opposite-right-inverse (refl _) = refl _

  -- This is useless in the presence of ap & equation reasioning combinators
  whisker-left : {x y z : A} (p : x ≡ y) {q r : y ≡ z}
    → (q ≡ r → p ∘ q ≡ p ∘ r)
  whisker-left p (refl _) = refl _

  -- This is useless in the presence of ap & equation reasioning combinators
  whisker-right : {x y z : A} (p : y ≡ z) {q r : x ≡ y}
    → (q ≡ r → q ∘ p ≡ r ∘ p)
  whisker-right p (refl _) = refl _

  anti-whisker-right : {x y z : A} (p : y ≡ z) {q r : x ≡ y}
    → (q ∘ p ≡ r ∘ p → q ≡ r)
  anti-whisker-right (refl _) {q} {r} h =
    ! (refl-right-unit q) ∘ (h ∘ refl-right-unit r)

  anti-whisker-left : {x y z : A} (p : x ≡ y) {q r : y ≡ z}
    → (p ∘ q ≡ p ∘ r → q ≡ r)
  anti-whisker-left (refl _) h = h

  -- [opposite-concat …] gives a result of the form [opposite (concat …) ≡ …],
  -- and so on
  opposite-concat : {x y z : A} (p : x ≡ y) (q : y ≡ z) → ! (p ∘ q) ≡ ! q ∘ ! p
  opposite-concat (refl _) q = ! (refl-right-unit (! q))

  concat-opposite : {x y z : A} (q : y ≡ z) (p : x ≡ y) → ! q ∘ ! p ≡ ! (p ∘ q)
  concat-opposite q (refl _) = refl-right-unit (! q)

  opposite-opposite : {x y : A} (p : x ≡ y) → ! (! p) ≡ p
  opposite-opposite (refl _) = refl _

-- Reduction rules for transport

module _ {i} {A : Set i} where
  -- This first part is about transporting something in a known fibration. In
  -- the names, [x] represents the variable of the fibration, [a] is a constant
  -- term, [A] is a constant type, and [f] and [g] are constant functions.

  trans-id≡cst : {a b c : A} (p : b ≡ c) (q : b ≡ a)
    → transport (λ x → x ≡ a) p q ≡ (! p) ∘ q
  trans-id≡cst (refl _) q = refl _

  trans-cst≡id : {a b c : A} (p : b ≡ c) (q : a ≡ b)
    → transport (λ x → a ≡ x) p q ≡ q ∘ p
  trans-cst≡id (refl _) q = ! (refl-right-unit q)

  trans-app≡app : ∀ {j} {B : Set j} (f g : A → B) {x y : A} (p : x ≡ y)
    (q : f x ≡ g x)
    → transport (λ x → f x ≡ g x) p q ≡ ! (map f p) ∘ (q ∘ map g p)
  trans-app≡app f g (refl _) q = ! (refl-right-unit q)

  trans-move-app≡app : ∀ {j} {B : Set j} (f g : A → B) {x y : A} (p : x ≡ y)
    (q : f x ≡ g x) {r : f y ≡ g y}
    → (q ∘ map g p ≡ map f p ∘ r → transport (λ x → f x ≡ g x) p q ≡ r)
  trans-move-app≡app f g (refl _) q h = ! (refl-right-unit q) ∘ h

  trans-cst≡app : ∀ {j} {B : Set j} (a : B) (f : A → B) {x y : A} (p : x ≡ y)
    (q : a ≡ f x)
    → transport (λ x → a ≡ f x) p q ≡ q ∘ map f p
  trans-cst≡app a f (refl _) q = ! (refl-right-unit q)

  trans-app≡cst : ∀ {j} {B : Set j} (f : A → B) (a : B) {x y : A} (p : x ≡ y)
    (q : f x ≡ a)
    → transport (λ x → f x ≡ a) p q ≡ ! (map f p) ∘ q
  trans-app≡cst f a (refl _) q = refl q

  trans-id≡app : (f : A → A) {x y : A} (p : x ≡ y) (q : x ≡ f x)
    → transport (λ x → x ≡ f x) p q ≡ ! p ∘ (q ∘ map f p)
  trans-id≡app f (refl _) q = ! (refl-right-unit q)

  trans-app≡id : (f : A → A) {x y : A} (p : x ≡ y) (q : f x ≡ x)
    → transport (λ x → f x ≡ x) p q ≡ ! (map f p) ∘ (q ∘ p)
  trans-app≡id f (refl _) q = ! (refl-right-unit q)

  trans-id≡id : {x y : A} (p : x ≡ y) (q : x ≡ x)
    → transport (λ x → x ≡ x) p q ≡ ! p ∘ (q ∘ p)
  trans-id≡id (refl _) q = ! (refl-right-unit _)

  trans-cst : ∀ {j} {B : Set j} {x y : A} (p : x ≡ y) (q : B)
    → transport (λ _ → B) p q ≡ q
  trans-cst (refl _) q = refl _

  trans-Π2 : ∀ {j k} (B : Set j) (P : (x : A) (y : B) → Set k)
    {b c : A} (p : b ≡ c) (q : (y : B) → P b y) (a : B)
    → transport (λ x → ((y : B) → P x y)) p q a
      ≡ transport (λ u → P u a) p (q a)
  trans-Π2 B P (refl _) q a = refl _

  trans-→-trans : ∀ {j k} (B : A → Set j) (P : A → Set k)
    {b c : A} (p : b ≡ c) (q : B b → P b) (a : B b)
    → transport (λ x → B x → P x) p q (transport B p a)
      ≡ transport P p (q a)
  trans-→-trans B P (refl _) q a = refl _

  trans-→ : ∀ {j k} (B : A → Set j) (P : A → Set k)
    {b c : A} (p : b ≡ c) (q : B b → P b) (a : B c)
    → transport (λ x → B x → P x) p q a
      ≡ transport P p (q $ transport B (! p) a)
  trans-→ B P (refl _) q a = refl _

  -- This second part is about transporting something along a known path

  trans-diag : ∀ {j} (P : A → A → Set j) {x y : A} (p : x ≡ y) (q : P x x)
    → transport (λ x → P x x) p q ≡ transport (λ z → P z y) p (transport (P x) p q)
  trans-diag P (refl _) q = refl _

  trans-concat : ∀ {j} (P : A → Set j) {x y z : A} (p : y ≡ z) (q : x ≡ y)
    (u : P x)
    → transport P (q ∘ p) u ≡ transport P p (transport P q u)
  trans-concat P p (refl _) u = refl _

  compose-trans : ∀ {j} (P : A → Set j) {x y z : A} (p : y ≡ z) (q : x ≡ y)
    (u : P x)
    →  transport P p (transport P q u) ≡ transport P (q ∘ p) u
  compose-trans P p (refl _) u = refl _

  trans-ap : ∀ {j k} {B : Set j} (P : B → Set k) (f : A → B)
    {x y : A} (p : x ≡ y) (u : P (f x))
    → transport P (ap f p) u ≡ transport (P ◯ f) p u
  trans-ap P f (refl _) u = refl _

  trans-map : ∀ {j k} {B : Set j} (P : B → Set k) (f : A → B)
    {x y : A} (p : x ≡ y) (u : P (f x))
    → transport P (map f p) u ≡ transport (P ◯ f) p u
  trans-map = trans-ap

  -- Unreadable, should be removed
  trans-totalpath : ∀ {j k} (P : A → Set j) (Q : Σ A P → Set k) {x y : Σ A P}
    (p : π₁ x ≡ π₁ y) (q : transport P p (π₂ x) ≡ π₂ y)
    (f : (t : P (π₁ x)) → Q (π₁ x , t))
    → transport Q (Σ-eq p q) (f (π₂ x)) ≡
        transport (λ x' → Q (π₁ y , x')) q
          (transport (λ x' → (t : P x') → Q (x' , t)) p f
            (transport P p (π₂ x)))
  trans-totalpath P Q {(x₁ , x₂)} {(y₁ , y₂)} p q f =
    trans-totalpath' P Q {x₁} {y₁} {x₂} {y₂} p q f where

    trans-totalpath' : ∀ {j k} (P : A → Set j) (Q : Σ A P → Set k) {x₁ y₁ : A}
      {x₂ : P x₁} {y₂ : P y₁}
      (p : x₁ ≡ y₁) (q : transport P p (x₂) ≡ y₂) (f : (t : P x₁) → Q (x₁ , t))
      → transport Q (Σ-eq p q) (f x₂) ≡
          transport (λ x' → Q (y₁ , x')) q
            (transport (λ x' → (t : P x') → Q (x' , t)) p f
              (transport P p x₂))
    trans-totalpath' P Q (refl _) (refl _) f = refl _

  -- This third part is about various other convenient properties

  trans-trans-opposite : ∀ {j} (P : A → Set j) {x y : A} (p : x ≡ y) (u : P y)
    → transport P p (transport P (! p) u) ≡ u
  trans-trans-opposite P (refl _) u = refl u

  trans-opposite-trans : ∀ {j} (P : A → Set j) {x y : A} (p : x ≡ y) (u : P x)
    → transport P (! p) (transport P p u) ≡ u
  trans-opposite-trans P (refl _) u = refl u

  map-dep-trivial : ∀ {j} {B : Set j} (f : A → B) {x y : A} (p : x ≡ y)
    → map f p ≡ ! (trans-cst p (f x)) ∘ map-dep f p
  map-dep-trivial f (refl _) = refl _

  homotopy-naturality : ∀ {j} {B : Set j} (f g : A → B)
    (p : (x : A) → f x ≡ g x) {x y : A} (q : x ≡ y)
    → map f q ∘ p y ≡ p x ∘ map g q
  homotopy-naturality f g p (refl _) = ! (refl-right-unit _)

  homotopy-naturality-toid : (f : A -> A) (p : (x : A) → f x ≡ x)
    {x y : A} (q : x ≡ y) → map f q ∘ p y ≡ p x ∘ q
  homotopy-naturality-toid f p (refl _) = ! (refl-right-unit _)

  homotopy-naturality-fromid : (g : A -> A) (p : (x : A) → x ≡ g x)
    {x y : A} (q : x ≡ y) → q ∘ p y ≡ p x ∘ map g q
  homotopy-naturality-fromid g p (refl _) = ! (refl-right-unit _)

  opposite-map : ∀ {j} {B : Set j} (f : A → B) {x y : A} (p : x ≡ y)
    → ! (map f p) ≡ map f (! p)
  opposite-map f (refl _) = refl _

  opposite-ap : ∀ {j} {B : Set j} (f : A → B) {x y : A} (p : x ≡ y)
    → ! (ap f p) ≡ ap f (! p)
  opposite-ap f (refl _) = refl _

  map-opposite : ∀ {j} {B : Set j} (f : A → B) {x y : A} (p : x ≡ y)
    → map f (! p) ≡ ! (map f p)
  map-opposite f (refl _) = refl _

  ap-opposite : ∀ {j} {B : Set j} (f : A → B) {x y : A} (p : x ≡ y)
    → ap f (! p) ≡ ! (ap f p)
  ap-opposite f (refl _) = refl _

  concat-map : ∀ {j} {B : Set j} (f : A → B) {x y z : A} (p : x ≡ y) (q : y ≡ z)
    → map f p ∘ map f q ≡ map f (p ∘ q)
  concat-map f (refl _) _ = refl _

  concat-ap : ∀ {j} {B : Set j} (f : A → B) {x y z : A} (p : x ≡ y) (q : y ≡ z)
    → map f p ∘ map f q ≡ map f (p ∘ q)
  concat-ap f (refl _) _ = refl _

  map-concat : ∀ {j} {B : Set j} (f : A → B) {x y z : A} (p : x ≡ y) (q : y ≡ z)
    → map f (p ∘ q) ≡ map f p ∘ map f q
  map-concat f (refl _) _ = refl _

  compose-map : ∀ {j k} {B : Set j} {C : Set k} (g : B → C) (f : A → B)
    {x y : A} (p : x ≡ y) → map g (map f p) ≡ map (g ◯ f) p
  compose-map f g (refl _) = refl _

  map-compose : ∀ {j k} {B : Set j} {C : Set k} (g : B → C) (f : A → B)
    {x y : A} (p : x ≡ y) → map (g ◯ f) p ≡ map g (map f p)
  map-compose f g (refl _) = refl _

  ap-compose : ∀ {j k} {B : Set j} {C : Set k} (g : B → C) (f : A → B)
    {x y : A} (p : x ≡ y) → ap (g ◯ f) p ≡ ap g (ap f p)
  ap-compose f g (refl _) = refl _

  map-cst : ∀ {j} {B : Set j} (b : B) {x y : A} (p : x ≡ y)
    → map (cst b) p ≡ refl b
  map-cst b (refl _) = refl _

  map-id : {u v : A} (p : u ≡ v) → map (id A) p ≡ p
  map-id (refl _) = refl _

  app-trans : ∀ {j k} (B : A → Set j) (C : A → Set k) (f : ∀ x → B x → C x)
    {x y} (p : x ≡ y) (a : B x)
    → f y (transport B p a) ≡ transport C p (f x a)
  app-trans B C f (refl _) a = refl _


  -- Move functions
  -- These functions are used when the goal is to show that path is a
  -- concatenation of two other paths, and that you want to prove it by moving a
  -- path to the other side
  --
  -- The first [left/right] is the side (with respect to ≡) where will be the
  -- path after moving (“after” means “after replacing the conclusion of the
  -- proposition by its premisse”), and the second [left/right] is the side
  -- (with respect to ∘) where the path is (and will still be)
  -- If you want to prove something of the form [p ≡ q ∘ r] by moving [q] or [r]
  -- to the left,  use the functions move-left-on-left  and move-left-on-right
  -- If you want to prove something of the form [p ∘ q ≡ r] by moving [p] or [q]
  -- to the right, use the functions move-right-on-left and move-right-on-right
  -- Add a [0] after [move] if the big path is constant, a [1] if the other
  -- small path is constant and then a [!] if the path you will move is an
  -- opposite.
  --
  -- I’m not sure all of these functions are useful, but it can’t hurt to have
  -- them.

  move-left-on-left : {x y z : A} (p : x ≡ z) (q : x ≡ y) (r : y ≡ z)
    → ((! q) ∘ p ≡ r → p ≡ q ∘ r)
  move-left-on-left p (refl _) r h = h

  move-left-on-right : {x y z : A} (p : x ≡ z) (q : x ≡ y) (r : y ≡ z)
    → (p ∘ (! r) ≡ q → p ≡ q ∘ r)
  move-left-on-right p q (refl _) h = ! (refl-right-unit p)
                                      ∘ (h ∘ ! (refl-right-unit q))

  move-right-on-left : {x y z : A} (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
    → (q ≡ (! p) ∘ r → p ∘ q ≡ r)
  move-right-on-left (refl _) q r h = h

  move-right-on-right : {x y z : A} (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
    → (p ≡ r ∘ (! q) → p ∘ q ≡ r)
  move-right-on-right p (refl _) r h = refl-right-unit p
                                       ∘ (h ∘ refl-right-unit r)

  move!-left-on-left : {x y z : A} (p : x ≡ z) (q : y ≡ x) (r : y ≡ z)
    → (q ∘ p ≡ r → p ≡ (! q) ∘ r)
  move!-left-on-left p (refl _) r h = h

  move!-left-on-right : {x y z : A} (p : x ≡ z) (q : x ≡ y) (r : z ≡ y)
    → (p ∘ r ≡ q → p ≡ q ∘ (! r))
  move!-left-on-right p q (refl _) h = ! (refl-right-unit p)
                                       ∘ (h ∘ ! (refl-right-unit q))

  move!-right-on-left : {x y z : A} (p : y ≡ x) (q : y ≡ z) (r : x ≡ z)
    → (q ≡ p ∘ r → (! p) ∘ q ≡ r)
  move!-right-on-left (refl _) q r h = h

  move!-right-on-right : {x y z : A} (p : x ≡ y) (q : z ≡ y) (r : x ≡ z)
    → (p ≡ r ∘ q → p ∘ (! q) ≡ r)
  move!-right-on-right p (refl _) r h = refl-right-unit p
                                        ∘ (h ∘ refl-right-unit r)

  move0-left-on-left : {x y : A} (q : x ≡ y) (r : y ≡ x)
    → (! q ≡ r → refl x ≡ q ∘ r)
  move0-left-on-left (refl _) r h = h

  move0-left-on-right : {x y : A} (q : x ≡ y) (r : y ≡ x)
    → (! r ≡ q → refl x ≡ q ∘ r)
  move0-left-on-right q (refl _) h = h ∘ ! (refl-right-unit q)

  move0-right-on-left : {x y : A} (p : x ≡ y) (q : y ≡ x)
    → (q ≡ ! p → p ∘ q ≡ refl x)
  move0-right-on-left (refl _) q h = h

  move0-right-on-right : {x y : A} (p : x ≡ y) (q : y ≡ x)
    → (p ≡ ! q → p ∘ q ≡ refl x)
  move0-right-on-right p (refl _) h = refl-right-unit p ∘ h

  move0!-left-on-left : {x y : A} (q : y ≡ x) (r : y ≡ x)
    → (q ≡ r → refl x ≡ (! q) ∘ r)
  move0!-left-on-left (refl _) r h = h

  move0!-left-on-right : {x y : A} (q : x ≡ y) (r : x ≡ y)
    → (r ≡ q → refl x ≡ q ∘ (! r))
  move0!-left-on-right q (refl _) h = h ∘ ! (refl-right-unit q)

  move0!-right-on-left : {x y : A} (p : y ≡ x) (q : y ≡ x)
    → (q ≡ p → (! p) ∘ q ≡ refl x)
  move0!-right-on-left (refl _) q h = h

  move0!-right-on-right : {x y z : A} (p : x ≡ y) (q : x ≡ y)
    → (p ≡ q → p ∘ (! q) ≡ refl x)
  move0!-right-on-right p (refl _) h = refl-right-unit p ∘ h

  move1-left-on-left : {x y : A} (p : x ≡ y) (q : x ≡ y)
    → ((! q) ∘ p ≡ refl y → p ≡ q)
  move1-left-on-left p (refl _) h = h

  move1-left-on-right : {x y : A} (p : x ≡ y) (r : x ≡ y)
    → (p ∘ (! r) ≡ refl x → p ≡ r)
  move1-left-on-right p (refl _) h = ! (refl-right-unit p) ∘ h

  move1-right-on-left : {x y : A} (p : x ≡ y) (r : x ≡ y)
    → (refl y ≡ (! p) ∘ r → p ≡ r)
  move1-right-on-left (refl _) r h = h

  move1-right-on-right : {x y : A} (q : x ≡ y) (r : x ≡ y)
    → (refl x ≡ r ∘ (! q) → q ≡ r)
  move1-right-on-right (refl _) r h = h ∘ refl-right-unit r

  move1!-left-on-left : {x y : A} (p : x ≡ y) (q : y ≡ x)
    → (q ∘ p ≡ refl y → p ≡ ! q)
  move1!-left-on-left p (refl _) h = h

  move1!-left-on-right : {x y : A} (p : x ≡ y) (r : y ≡ x)
    → (p ∘ r ≡ refl x → p ≡ ! r)
  move1!-left-on-right p (refl _) h = ! (refl-right-unit p) ∘ h

  move1!-right-on-left : {x y : A} (p : y ≡ x) (r : x ≡ y)
    → (refl y ≡ p ∘ r → ! p ≡ r)
  move1!-right-on-left (refl _) r h = h

  move1!-right-on-right : {x y : A} (q : y ≡ x) (r : x ≡ y)
    → (refl x ≡ r ∘ q → ! q ≡ r)
  move1!-right-on-right (refl _) r h = h ∘ refl-right-unit r


  move-transp-left : ∀ {j} (P : A → Set j) {x y : A} (u : P y) (p : x ≡ y)
    (v : P x)
    → transport P (! p) u ≡ v → u ≡ transport P p v
  move-transp-left P _ (refl _) _ p = p

  move-transp-right : ∀ {j} (P : A → Set j) {x y : A} (p : y ≡ x) (u : P y)
    (v : P x)
    → u ≡ transport P (! p) v → transport P p u ≡ v
  move-transp-right P (refl _) _ _ p = p

  move!-transp-left : ∀ {j} (P : A → Set j) {x y : A} (u : P y) (p : y ≡ x)
    (v : P x)
    → transport P p u ≡ v → u ≡ transport P (! p) v
  move!-transp-left P _ (refl _) _ p = p

  move!-transp-right : ∀ {j} (P : A → Set j) {x y : A} (p : x ≡ y) (u : P y)
    (v : P x)
    → u ≡ transport P p v → transport P (! p) u ≡ v
  move!-transp-right P (refl _) _ _ p = p
