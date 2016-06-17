{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NConnected
open import lib.types.Bool
open import lib.types.Lift
open import lib.types.Nat
open import lib.types.Pointed
open import lib.types.TLevel
open import lib.types.Suspension

module lib.types.IteratedSuspension where

⊙Susp^ : ∀ {i} (n : ℕ) → Ptd i → Ptd i
⊙Susp^ O X = X
⊙Susp^ (S n) X = ⊙Susp (⊙Susp^ n X)

⊙Susp^-conn : ∀ {i} (n : ℕ) {X : Ptd i} {m : ℕ₋₂}
  → is-connected m (fst X) → is-connected (⟨ n ⟩₋₂ +2+ m) (fst (⊙Susp^ n X))
⊙Susp^-conn O cX = cX
⊙Susp^-conn (S n) cX = Susp-conn (⊙Susp^-conn n cX)

⊙Susp^-+ : ∀ {i} (m n : ℕ) {X : Ptd i}
  → ⊙Susp^ m (⊙Susp^ n X) == ⊙Susp^ (m + n) X
⊙Susp^-+ O n = idp
⊙Susp^-+ (S m) n = ap ⊙Susp (⊙Susp^-+ m n)

⊙susp^-fmap : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → fst (X ⊙→ Y) → fst (⊙Susp^ n X ⊙→ ⊙Susp^ n Y)
⊙susp^-fmap O f = f
⊙susp^-fmap (S n) f = ⊙susp-fmap (⊙susp^-fmap n f)

⊙susp^-fmap-idf : ∀ {i} (n : ℕ) (X : Ptd i)
  → ⊙susp^-fmap n (⊙idf X) == ⊙idf (⊙Susp^ n X)
⊙susp^-fmap-idf O X = idp
⊙susp^-fmap-idf (S n) X =
  ap ⊙susp-fmap (⊙susp^-fmap-idf n X) ∙ ⊙susp-fmap-idf (⊙Susp^ n X)

⊙susp^-fmap-cst : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → ⊙susp^-fmap n (⊙cst {X = X} {Y = Y}) == ⊙cst
⊙susp^-fmap-cst O = idp
⊙susp^-fmap-cst (S n) = ap ⊙susp-fmap (⊙susp^-fmap-cst n)
                           ∙ (⊙susp-fmap-cst {X = ⊙Susp^ n _})

⊙susp^-fmap-∘ : ∀ {i j k} (n : ℕ) {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (g : fst (Y ⊙→ Z)) (f : fst (X ⊙→ Y))
  → ⊙susp^-fmap n (g ⊙∘ f) == ⊙susp^-fmap n g ⊙∘ ⊙susp^-fmap n f
⊙susp^-fmap-∘ O g f = idp
⊙susp^-fmap-∘ (S n) g f =
  ap ⊙susp-fmap (⊙susp^-fmap-∘ n g f)
  ∙ ⊙susp-fmap-∘ (⊙susp^-fmap n g) (⊙susp^-fmap n f)


⊙Sphere : (n : ℕ) → Ptd₀
⊙Sphere n = ⊙Susp^ n ⊙Bool

Sphere : (n : ℕ) → Type₀
Sphere n = fst (⊙Sphere n)

-- favonia: [S¹] has its own elim rules in Circle.agda.
⊙S⁰ = ⊙Sphere 0
⊙S¹ = ⊙Sphere 1
⊙S² = ⊙Sphere 2
⊙S³ = ⊙Sphere 3
S⁰ = Sphere 0
S¹ = Sphere 1
S² = Sphere 2
S³ = Sphere 3
