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

⊙Susp^-fmap : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → X ⊙→ Y → ⊙Susp^ n X ⊙→ ⊙Susp^ n Y
⊙Susp^-fmap O f = f
⊙Susp^-fmap (S n) f = ⊙Susp-fmap (⊙Susp^-fmap n f)

⊙Susp^-fmap-idf : ∀ {i} (n : ℕ) (X : Ptd i)
  → ⊙Susp^-fmap n (⊙idf X) == ⊙idf (⊙Susp^ n X)
⊙Susp^-fmap-idf O X = idp
⊙Susp^-fmap-idf (S n) X =
  ap ⊙Susp-fmap (⊙Susp^-fmap-idf n X) ∙ ⊙Susp-fmap-idf (⊙Susp^ n X)

⊙Susp^-fmap-cst : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → ⊙Susp^-fmap n (⊙cst {X = X} {Y = Y}) == ⊙cst
⊙Susp^-fmap-cst O = idp
⊙Susp^-fmap-cst (S n) = ap ⊙Susp-fmap (⊙Susp^-fmap-cst n)
                           ∙ (⊙Susp-fmap-cst {X = ⊙Susp^ n _})

⊙Susp^-fmap-∘ : ∀ {i j k} (n : ℕ) {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (g : Y ⊙→ Z) (f : X ⊙→ Y)
  → ⊙Susp^-fmap n (g ⊙∘ f) == ⊙Susp^-fmap n g ⊙∘ ⊙Susp^-fmap n f
⊙Susp^-fmap-∘ O g f = idp
⊙Susp^-fmap-∘ (S n) g f =
  ap ⊙Susp-fmap (⊙Susp^-fmap-∘ n g f)
  ∙ ⊙Susp-fmap-∘ (⊙Susp^-fmap n g) (⊙Susp^-fmap n f)

⊙Susp^-Susp-split-iso : ∀ {i} (n : ℕ) (X : Ptd i)
  → ⊙Susp^ (S n) X ⊙≃ ⊙Susp^ n (⊙Susp X)
⊙Susp^-Susp-split-iso O     X = ⊙ide _
⊙Susp^-Susp-split-iso (S n) X = ⊙Susp-emap (⊙Susp^-Susp-split-iso n X)


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
