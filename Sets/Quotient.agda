{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.TruncatedHIT
open import Spaces.Spheres
open import Integers

module Sets.Quotient {i j} (A : Set i) ⦃ p : is-set A ⦄
  (R : A → A → Set j) ⦃ q : (x y : A) → is-prop (R x y) ⦄ where

private
  data _#/_ : Set (max i j) where
    #proj : A → _#/_

    #top : (f : hSⁿ ⟨0⟩ → _#/_) → _#/_

_/_ : Set (max i j)
_/_ = _#/_

proj : A → _/_
proj = #proj

postulate  -- HIT
  eq : (x y : A) (p : R x y) → proj x ≡ proj y

top : (f : hSⁿ ⟨0⟩ → _/_) → _/_
top = #top

postulate  -- HIT
  rays : (f : hSⁿ ⟨0⟩ → _/_) (x : hSⁿ ⟨0⟩) → top f ≡ f x

#/-rec : ∀ {k} (P : _/_ → Set k)
  (proj* : (x : A) → P (proj x))
  (eq* : (x y : A) (p : R x y) → transport P (eq x y p) (proj* x) ≡ proj* y)
  (top* : (f : hSⁿ ⟨0⟩ → _/_) (p : (x : hSⁿ ⟨0⟩) → P (f x)) → P (top f))
  (rays* : (f : hSⁿ ⟨0⟩ → _/_) (p : (x : hSⁿ ⟨0⟩) → P (f x)) (x : hSⁿ ⟨0⟩)
         → transport P (rays f x) (top* f p) ≡ p x)
  → ((t : _/_) → P t)
#/-rec P proj* eq* top* rays* (#proj x) = proj* x
#/-rec P proj* eq* top* rays* (#top f) =
  top* f (λ x → #/-rec P proj* eq* top* rays* (f x))

#/-rec-nondep : ∀ {k} (B : Set k)
  (proj* : A → B)
  (eq* : (x y : A) (p : R x y) → proj* x ≡ proj* y)
  (top* : (f : hSⁿ ⟨0⟩ → _/_) (p : hSⁿ ⟨0⟩ → B) → B)
  (rays* : (f : hSⁿ ⟨0⟩ → _/_) (p : hSⁿ ⟨0⟩ → B) (x : hSⁿ ⟨0⟩) → top* f p ≡ p x)
  → (_/_ → B)
#/-rec-nondep B proj* eq* top* rays* (#proj x) = proj* x
#/-rec-nondep B proj* eq* top* rays* (#top f) =
  top* f (λ x → #/-rec-nondep B proj* eq* top* rays* (f x))


/-rec :  ∀ {k} (P : _/_ → Set k)
  (proj* : (x : A) → P (proj x))
  (eq* : (x y : A) (p : R x y) → transport P (eq x y p) (proj* x) ≡ proj* y)
  (trunc : (x : _/_) → is-set (P x))
  → ((t : _/_) → P t)
/-rec P proj* eq* trunc = #/-rec P proj* eq*
                                 (λ f p₁ → π₁ (u f p₁))
                                 (λ f p₁ → π₂ (u f p₁)) where
  u : _
  u = truncated-has-filling-dep _/_ P ⟨0⟩ (λ ()) (λ f → (top f , rays f))

/-rec-nondep : ∀ {k} (B : Set k)
  (proj* : A → B)
  (eq* : (x y : A) (p : R x y) → proj* x ≡ proj* y)
  (trunc : is-set B)
  → (_/_ → B)
/-rec-nondep B proj* eq* trunc = #/-rec-nondep B proj* eq*
                                               (λ _ p → π₁ (u p))
                                               (λ _ p → π₂ (u p)) where
  u : _
  u = truncated-has-spheres-filled ⟨0⟩ _ trunc

-- Reduction rules for paths are not needed
