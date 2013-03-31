{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Truncation

-- Loop space commutes with truncation in the sense that
-- τ n (Ω X) = Ω (τ (S n) X)
-- (actually, this is true more generally for paths spaces and we need this
-- level of generality to prove it)

module Homotopy.PathTruncation {i} {n : ℕ₋₂} {A : Set i} where

private
  to : (x y : A) → (τ n (x ≡ y)) → ((proj {n = S n} x) ≡ (proj y))
  to x y = τ-extend-nondep ⦃ τ-is-truncated (S n) A _ _ ⦄ (map proj)

  -- [truncated-path-space (proj x) (proj y)] is [τ n (x ≡ y)]
  truncated-path-space : (u v : τ (S n) A) → Type≤ n i
  truncated-path-space = τ-extend-nondep
                           ⦃ →-is-truncated (S n) (Type≤-is-truncated n _) ⦄
                           (λ x → τ-extend-nondep ⦃ Type≤-is-truncated n _ ⦄
                             (λ y → τ n (x ≡ y) , τ-is-truncated n _))

  -- We now extend [to] to the truncation of [A], and this is why we needed to
  -- first extend the return type of [to]
  to' : (u v : τ (S n) A) → (π₁ (truncated-path-space u v) → u ≡ v)
  to' = τ-extend ⦃ λ x → Π-is-truncated (S n) (λ a →
                           Π-is-truncated (S n) (λ b →
                             ≡-is-truncated (S n)
                               (τ-is-truncated (S n) A)))⦄
          (λ x → τ-extend ⦃ λ t → Π-is-truncated (S n) (λ a →
                                    ≡-is-truncated (S n)
                                      (τ-is-truncated (S n) A))⦄
            (λ y → to x y))

  from'-refl : (u : τ (S n) A) → (π₁ (truncated-path-space u u))
  from'-refl = τ-extend ⦃ λ x → truncated-is-truncated-S n
                                  (π₂ (truncated-path-space x x))⦄
                 (λ x → proj (refl x))

  from' : (u v : τ (S n) A) → (u ≡ v → π₁ (truncated-path-space u v))
  from' u .u (refl .u) = from'-refl u

  from : (x y : A) → (proj {n = S n} x ≡ proj y → τ n (x ≡ y))
  from x y p = from' (proj x) (proj y) p

  from-to : (x y : A) (p : τ n (x ≡ y)) → from x y (to x y p) ≡ p
  from-to x y = τ-extend ⦃ λ _ → ≡-is-truncated n (τ-is-truncated n _)⦄
                  (from-to' x y) where

    from-to' : (x y : A) (p : x ≡ y) → from x y (to x y (proj p)) ≡ proj p
    from-to' x .x (refl .x) = refl _

  to'-from' : (u v : τ (S n) A) (p : u ≡ v) → to' u v (from' u v p) ≡ p
  to'-from' x .x (refl .x) = to'-from'-refl x where
    to'-from'-refl : (u : τ (S n) A) → to' u u (from' u u (refl u)) ≡ refl u
    to'-from'-refl = τ-extend ⦃ λ _ → ≡-is-truncated (S n)
                                        (≡-is-truncated (S n)
                                          (τ-is-truncated (S n) A))⦄
                       (λ _ → refl _)

  to-from : (x y : A) (p : proj {n = S n} x ≡ proj y) → to x y (from x y p) ≡ p
  to-from x y p = to'-from' (proj x) (proj y) p

τ-path-equiv-path-τ-S : {x y : A} → τ n (x ≡ y) ≃ (proj {n = S n} x ≡ proj y)
τ-path-equiv-path-τ-S {x} {y} =
  (to x y , iso-is-eq _ (from x y) (to-from x y) (from-to x y))

module _ where
  open import Homotopy.Connected

  connected-has-all-τ-paths : is-connected (S n) A → (p q : A) → τ n (p ≡ q)
  connected-has-all-τ-paths (_ , path) p q = inverse τ-path-equiv-path-τ-S
    $ path (proj p) ∘ ! (path $ proj q)
