{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.TruncatedHIT
open import Sets.Quotient

module Sets.QuotientUP {i j} (A : Set i) ⦃ A-set : is-set A ⦄
  (R : A → A → Set j) ⦃ R-prop : (x y : A) → is-prop (R x y) ⦄ where

-- [X →→ Y ~ R] is the set of functions [X → Y] respecting the relation [R]
_→→_~_ : ∀ {i j k}
  (X : Set i) ⦃ X-set : is-set X ⦄
  (Y : Set j) ⦃ Y-set : is-set Y ⦄
  (R : X → X → Set k) ⦃ R-prop : (x x' : X) → is-prop (R x x')⦄
    → Set _
X →→ Y ~ R = Σ (X → Y) (λ f → (x x' : X) → (R x x' → f x ≡ f x'))

module UP {k} (B : Set k) (B-set : is-set B) where

  factor : ((A →→ B ~ R) → (A / R → B))
  factor (f , p) = /-rec-nondep A R B f p B-set

  extend : ((A / R → B) → (A →→ B ~ R))
  extend f = ((f ◯ proj A R) , (λ x x' p₁ → ap f (eq A R x x' p₁)))

  extend-factor : (f : A →→ B ~ R) → extend (factor f) ≡ f
  extend-factor (f , p) = ap (λ x → f , x)
                           (funext (λ x →
                            funext (λ x' →
                            funext (λ p₁ → π₁ (B-set _ _ _ _)))))

  factor-extend : (f : A / R → B) → factor (extend f) ≡ f
  factor-extend f =
    funext (/-rec A R (λ x → factor (extend f) x ≡ f x)
           (λ x → refl)
           (λ x y _ → π₁ (B-set _ _ _ _))
           (λ x → truncated-is-truncated-S _ (B-set _ _)))
