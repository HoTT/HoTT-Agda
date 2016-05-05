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
realize : ∀ {i} {n : ℕ} → Skeleton {i} n → Type i

Skeleton {i} O = Type i
Skeleton {i} (S n) = Σ (Skeleton {i} n) (λ s → Σ (Type i) λ A → Boundry A (realize s) n i)

realize {n = O} A = A
realize {n = S n} (s , (A , boundary)) = Attach n boundary

⟦_⟧ = realize

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
cw-lift₁-equiv {n = n} skel = equiv to from to-from from-to
  where
    to : ⟦ cw-lift₁ skel ⟧ → ⟦ skel ⟧
    to = Attach-rec {n = n} (idf ⟦ skel ⟧) (λ{(lift ())}) (λ{(lift ()) _})

    from : ⟦ skel ⟧ → ⟦ cw-lift₁ skel ⟧
    from = ground {n = n}

    to-from : ∀ x → to (from x) == x
    to-from _ = idp

    from-to : ∀ x → from (to x) == x
    from-to = Attach-elim {n = n} (λ _ → idp) (λ{(lift ())}) (λ{(lift ()) _})

cw-lift : ∀ {i} {n m : ℕ} → n < m → Skeleton {i} n → Skeleton {i} m
cw-lift ltS = cw-lift₁
cw-lift (ltSR lt) = cw-lift₁ ∘ cw-lift lt
