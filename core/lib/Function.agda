{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.PathGroupoid

{-
This file contains various basic definitions and lemmas about functions
(non-dependent [Pi] types) that do not belong anywhere else.
-}

module lib.Function where

{- Basic lemmas about pointed maps -}

-- concatenation
⊙∘-pt : ∀ {i j} {A : Type i} {B : Type j}
  {a₁ a₂ : A} (f : A → B) {b : B}
  → a₁ == a₂ → f a₂ == b → f a₁ == b
⊙∘-pt f p q = ap f p ∙ q

infixr 30 _∼_ _⊙∼_
_∼_ : ∀ {i j} {A : Type i} {B : A → Type j}
  (f g : (a : A) → B a) → Type (lmax i j)
f ∼ g = ∀ x → f x == g x

{-
infixr 80 _∼-∙_

_∼-∙_ : ∀ {i j} {A : Type i} {B : Type j} {f g h : A → B}
  → f ∼ g → g ∼ h → f ∼ h
_∼-∙_ f∼g g∼h x = f∼g x ∙ g∼h x

∼-! : ∀ {i j} {A : Type i} {B : Type j} {f g : A → B}
  → f ∼ g → g ∼ f
∼-! f∼g = ! ∘ f∼g
-}

_⊙∼_ : ∀ {i j} {X : Ptd i} {Y : Ptd j}
  (f g : X ⊙→ Y) → Type (lmax i j)
_⊙∼_ {X = X} {Y = Y} (f , f-pt) (g , g-pt) =
  Σ (f ∼ g) λ p → f-pt == g-pt [ (_== pt Y) ↓ p (pt X) ]

{-
infixr 80 _⊙∼-∙_

_⊙∼-∙_ : ∀ {i j} {X : Ptd i} {Y : Ptd j} {f g h : X ⊙→ Y}
  → f ⊙∼ g → g ⊙∼ h → f ⊙∼ h
_⊙∼-∙_ f∼g g∼h = fst f∼g ∼-∙ fst g∼h , snd f∼g ∙ᵈ snd g∼h

⊙∼-! : ∀ {i j} {X : Ptd i} {Y : Ptd j} {f g : X ⊙→ Y}
  → f ⊙∼ g → g ⊙∼ f
⊙∼-! f∼g = ∼-! (fst f∼g) , !ᵈ (snd f∼g)
-}

infixr 80 _⊙∘_
_⊙∘_ : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (g : Y ⊙→ Z) (f : X ⊙→ Y) → X ⊙→ Z
(g , gpt) ⊙∘ (f , fpt) = (g ∘ f) , ⊙∘-pt g fpt gpt

⊙∘-unit-l : ∀ {i j} {X : Ptd i} {Y : Ptd j} (f : X ⊙→ Y)
  → ⊙idf Y ⊙∘ f ⊙∼ f
⊙∘-unit-l (f , idp) = (λ _ → idp) , idp

⊙∘-unit-r : ∀ {i j} {X : Ptd i} {Y : Ptd j} (f : X ⊙→ Y)
  → f ⊙∘ ⊙idf X ⊙∼ f
⊙∘-unit-r f = (λ _ → idp) , idp

{- Homotopy fibers -}

module _ {i j} {A : Type i} {B : Type j} (f : A → B) where

  hfiber : (y : B) → Type (lmax i j)
  hfiber y = Σ A (λ x → f x == y)

  {- Note that [is-inj] is not a mere proposition. -}
  is-inj : Type (lmax i j)
  is-inj = (a₁ a₂ : A) → f a₁ == f a₂ → a₁ == a₂

  preserves-≠ : Type (lmax i j)
  preserves-≠ = {a₁ a₂ : A} → a₁ ≠ a₂ → f a₁ ≠ f a₂

module _ {i j} {A : Type i} {B : Type j} {f : A → B} where
  abstract
    inj-preserves-≠ : is-inj f → preserves-≠ f
    inj-preserves-≠ inj ¬p q = ¬p (inj _ _ q)

module _ {i j k} {A : Type i} {B : Type j} {C : Type k}
  {f : A → B} {g : B → C} where

  ∘-is-inj : is-inj g → is-inj f → is-inj (g ∘ f)
  ∘-is-inj g-is-inj f-is-inj a₁ a₂ = f-is-inj a₁ a₂ ∘ g-is-inj (f a₁) (f a₂)

{- Maps between two functions -}

record CommSquare {i₀ i₁ j₀ j₁}
  {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
  (f₀ : A₀ → B₀) (f₁ : A₁ → B₁) (hA : A₀ → A₁) (hB : B₀ → B₁)
  : Type (lmax (lmax i₀ i₁) (lmax j₀ j₁)) where
  constructor comm-sqr
  field
    commutes : ∀ a₀ → (hB ∘ f₀) a₀ == (f₁ ∘ hA) a₀

open CommSquare public
