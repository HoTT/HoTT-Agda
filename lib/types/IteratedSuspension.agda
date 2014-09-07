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

Ptd-Susp^ : ∀ {i} (n : ℕ) → Ptd i → Ptd i
Ptd-Susp^ O X = X
Ptd-Susp^ (S n) X = Ptd-Susp (Ptd-Susp^ n X)

Ptd-Susp^-conn : ∀ {i} (n : ℕ) {X : Ptd i} {m : ℕ₋₂}
  → is-connected m (fst X) → is-connected ((n -2) +2+ m) (fst (Ptd-Susp^ n X))
Ptd-Susp^-conn O cX = cX
Ptd-Susp^-conn (S n) cX = Susp-conn (Ptd-Susp^-conn n cX)

Ptd-Susp^-+ : ∀ {i} (m n : ℕ) {X : Ptd i}
  → Ptd-Susp^ m (Ptd-Susp^ n X) == Ptd-Susp^ (m + n) X
Ptd-Susp^-+ O n = idp
Ptd-Susp^-+ (S m) n = ap Ptd-Susp (Ptd-Susp^-+ m n)

ptd-susp^-fmap : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → fst (X ∙→ Y) → fst (Ptd-Susp^ n X ∙→ Ptd-Susp^ n Y)
ptd-susp^-fmap O f = f
ptd-susp^-fmap (S n) f = ptd-susp-fmap (ptd-susp^-fmap n f)

ptd-susp^-fmap-idf : ∀ {i} (n : ℕ) (X : Ptd i)
  → ptd-susp^-fmap n (ptd-idf X) == ptd-idf (Ptd-Susp^ n X)
ptd-susp^-fmap-idf O X = idp
ptd-susp^-fmap-idf (S n) X =
  ap ptd-susp-fmap (ptd-susp^-fmap-idf n X) ∙ ptd-susp-fmap-idf (Ptd-Susp^ n X)

ptd-susp^-fmap-cst : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → ptd-susp^-fmap n (ptd-cst {X = X} {Y = Y}) == ptd-cst
ptd-susp^-fmap-cst O = idp
ptd-susp^-fmap-cst (S n) = ap ptd-susp-fmap (ptd-susp^-fmap-cst n)
                           ∙ (ptd-susp-fmap-cst {X = Ptd-Susp^ n _})

ptd-susp^-fmap-∘ : ∀ {i j k} (n : ℕ) {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (g : fst (Y ∙→ Z)) (f : fst (X ∙→ Y))
  → ptd-susp^-fmap n (g ∘ptd f) == ptd-susp^-fmap n g ∘ptd ptd-susp^-fmap n f
ptd-susp^-fmap-∘ O g f = idp
ptd-susp^-fmap-∘ (S n) g f =
  ap ptd-susp-fmap (ptd-susp^-fmap-∘ n g f)
  ∙ ptd-susp-fmap-∘ (ptd-susp^-fmap n g) (ptd-susp^-fmap n f)


Ptd-Sphere : ∀ {i} → (n : ℕ) → Ptd i
Ptd-Sphere n = Ptd-Susp^ n (Ptd-Lift Ptd-Bool)

Sphere : ∀ {i} → (n : ℕ) → Type i
Sphere n = fst (Ptd-Sphere n)
