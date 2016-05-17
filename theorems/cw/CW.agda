{-# OPTIONS --without-K #-}

{-
  Adapted from Ulrik's work in Lean (released under Apache License 2.0)
  https://github.com/leanprover/lean/blob/master/hott/homotopy/cellcomplex.hlean
-}

open import HoTT

module cw.CW where

open import cw.Attach public

-- skeleton

Skeleton : ∀ {i} → ℕ → Type (lsucc i)
Realizer : ∀ {i} {n : ℕ} → Skeleton {i} n → Type i

Skeleton {i} O = Type i
Skeleton {i} (S n) = Σ (Skeleton {i} n) (λ s → Σ (Type i) λ A → Boundry (Realizer s) A (Sphere {i} n))

Realizer {n = O} A = A
Realizer {n = S n} (s , (A , boundary)) = Attach boundary

⟦_⟧ = Realizer

-- Empty

CWEmpty-skel : Skeleton {lzero} 0
CWEmpty-skel = Empty
CWEmpty = ⟦ CWEmpty-skel ⟧

CWEmpty≃Empty : CWEmpty ≃ Empty
CWEmpty≃Empty = ide _

-- Unit

CWUnit-skel : Skeleton {lzero} 0
CWUnit-skel = Unit
CWUnit = ⟦ CWUnit-skel ⟧

CWUnit≃Unit : CWUnit ≃ Unit
CWUnit≃Unit = ide _

-- lifting

cw-lift₁ : ∀ {i} {n : ℕ} → Skeleton {i} n → Skeleton {i} (S n)
cw-lift₁ skel = skel , Lift Empty , λ{(lift ()) _}

-- This slightly extends the naming convension
-- to two skeletons being extensionally equal.
cw-lift₁-equiv : ∀ {i} {n} (skel : Skeleton {i} n)
  → ⟦ cw-lift₁ skel ⟧ ≃ ⟦ skel ⟧
cw-lift₁-equiv skel = equiv to incl to-incl incl-to
  where
    to : ⟦ cw-lift₁ skel ⟧ → ⟦ skel ⟧
    to = Attach-rec (idf ⟦ skel ⟧) (λ{(lift ())}) (λ{(lift ()) _})

    to-incl : ∀ x → to (incl x) == x
    to-incl _ = idp

    incl-to : ∀ x → incl (to x) == x
    incl-to = Attach-elim (λ _ → idp) (λ{(lift ())}) (λ{(lift ()) _})

cw-lift : ∀ {i} {n m : ℕ} → n < m → Skeleton {i} n → Skeleton {i} m
cw-lift ltS = cw-lift₁
cw-lift (ltSR lt) = cw-lift₁ ∘ cw-lift lt

cw-cells-top : ∀ {i} {n : ℕ} → Skeleton {i} n → Type i
cw-cells-top {n = O}   skel            = skel
cw-cells-top {n = S n} (_ , cells , _) = cells

-- Access the [i]th dimension

Sphere₋₁ : ∀ {i} → ℕ → Type i
Sphere₋₁ O = Lift Empty
Sphere₋₁ (S n) = Sphere n

realize₋₁ : ∀ {i} {n : ℕ} → Skeleton {i} n → Type i
realize₋₁ {n = O}   _          = Lift Empty
realize₋₁ {n = S n} (skel , _) = ⟦ skel ⟧

⟦_⟧₋₁ = realize₋₁

cw-boundary-top : ∀ {i} {n : ℕ} (s : Skeleton {i} n)
  → cw-cells-top s → (Sphere₋₁ {i} n → ⟦ s ⟧₋₁)
cw-boundary-top {n = O}    _                 = λ{_ (lift ())}
cw-boundary-top {n = S n} (_ , _ , boundary) = boundary

cw-cut : ∀ {i} {n : ℕ} (m : Bounded n) → Skeleton {i} n → Skeleton {i} (n -B m)
cw-cut O      skel      = skel
cw-cut (S n) (skel , _) = cw-cut n skel

-- Indexes are in reverse order.
cw-cells : ∀ {i} {n : ℕ} (m : Bounded n) → Skeleton {i} n → Type i
cw-cells m = cw-cells-top ∘ cw-cut m

cw-boundary : ∀ {i} {n : ℕ} (m : Bounded n) (skel : Skeleton {i} n)
  → cw-cells m skel → Sphere₋₁ (n -B m) → ⟦ cw-cut m skel ⟧₋₁
cw-boundary m = cw-boundary-top ∘ cw-cut m
