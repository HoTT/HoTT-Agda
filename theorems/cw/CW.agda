{-# OPTIONS --without-K #-}

{-
  Adapted from Ulrik's work in Lean (released under Apache License 2.0)
  https://github.com/leanprover/lean/blob/master/hott/homotopy/cellcomplex.hlean
-}

open import HoTT

module cw.CW {i} where

open import cw.Attached public

{-
  Naming convension: most of them have the "cw-" prefix
-}

-- skeleton

data Skeleton : ℕ → Type (lsucc i)
Realizer : {n : ℕ} → Skeleton n → Type i

data Skeleton where
  skel-base : hSet i → Skeleton O
  skel-attach : ∀ {n} (skel : Skeleton n) (cells : hSet i)
    → Attaching (Realizer skel) (fst cells) (Sphere n)
    → Skeleton (S n)

Realizer (skel-base A) = fst A
Realizer (skel-attach s _ α) = Attached α

⟦_⟧ = Realizer

-- Take a prefix of a skeleton

cw-take : ∀ {m n : ℕ} (m≤n : m ≤ n) → Skeleton n → Skeleton m
cw-take (inl idp)        skel                   = skel
cw-take (inr ltS)        (skel-attach skel _ _) = skel
cw-take (inr (ltSR m≤n)) (skel-attach skel _ _) = cw-take (inr m≤n) skel

cw-head : ∀ {n : ℕ} → Skeleton n → hSet i
cw-head (skel-base   pts)      = pts
cw-head (skel-attach skel _ _) = cw-head skel

incl^ : ∀ {n : ℕ} (skel : Skeleton n)
  → fst (cw-head skel) → ⟦ skel ⟧
incl^ (skel-base _)       c = c
incl^ (skel-attach s _ _) c = incl (incl^ s c)

-- Pointedness

⊙Skeleton : ℕ → Type (lsucc i)
⊙Skeleton n = Σ (Skeleton n) (fst ∘ cw-head)

⊙Realizer : {n : ℕ} → ⊙Skeleton n → Ptd i
⊙Realizer (skel , pt) = ⟦ skel ⟧ , incl^ skel pt

⊙⟦_⟧ = ⊙Realizer

-- Access the [m]th cells

cells-last : ∀ {n : ℕ} → Skeleton n → hSet i
cells-last (skel-base     cells)   = cells
cells-last (skel-attach _ cells _) = cells

cells-nth : ∀ {m n : ℕ} (m≤n : m ≤ n) → Skeleton n → hSet i
cells-nth m≤n = cells-last ∘ cw-take m≤n

-- Access the [m]th dimensional attaching map

Sphere₋₁ : ℕ → Type₀
Sphere₋₁ O = Empty
Sphere₋₁ (S n) = Sphere n

Realizer₋₁ : ∀ {n : ℕ} → Skeleton n → Type i
Realizer₋₁ (skel-base _)          = Lift Empty
Realizer₋₁ (skel-attach skel _ _) = ⟦ skel ⟧

⟦_⟧₋₁ = Realizer₋₁

attaching-last : ∀ {n : ℕ} (s : Skeleton n)
  → fst (cells-last s) → (Sphere₋₁ n → ⟦ s ⟧₋₁)
attaching-last (skel-base _)               = λ{_ ()}
attaching-last (skel-attach _ _ attaching) = attaching

attaching-nth : ∀ {m n : ℕ} (m≤n : m ≤ n) (skel : Skeleton n)
  → fst (cells-nth m≤n skel) → Sphere₋₁ m → ⟦ cw-take m≤n skel ⟧₋₁
attaching-nth m≤n = attaching-last ∘ cw-take m≤n

-- Extra conditions on CW complexes

-- 1. decidable equalities
has-cells-with-dec-eq : ∀ {n} → Skeleton n → Type i
has-cells-with-dec-eq (skel-base cells) = has-dec-eq (fst cells)
has-cells-with-dec-eq (skel-attach skel cells _) =
  has-cells-with-dec-eq skel × has-dec-eq (fst cells)

has-cells-with-dec-eq-is-prop : ∀ {n} {skel : Skeleton n}
  → is-prop (has-cells-with-dec-eq skel)
has-cells-with-dec-eq-is-prop {skel = skel-base _} =
  has-dec-eq-is-prop
has-cells-with-dec-eq-is-prop {skel = skel-attach _ _ _} =
  ×-level has-cells-with-dec-eq-is-prop has-dec-eq-is-prop

-- 2. choice
has-cells-with-choice : (t : TLevel) {n : ℕ} (skel : Skeleton n)
  (j : ULevel) → Type (lmax i (lsucc j))
has-cells-with-choice t (skel-base cells) j = has-choice t (fst cells) j
has-cells-with-choice t (skel-attach skel cells _) j =
  has-cells-with-choice t skel j × has-choice t (fst cells) j

-- Dimensional lifting

cw-lift₁ : ∀ {n : ℕ} → Skeleton n → Skeleton (S n)
cw-lift₁ skel = skel-attach skel
  (Lift Empty , Lift-level Empty-is-set)
  λ{(lift ()) _}

-- This slightly extends the naming convension
-- to two skeletons being extensionally equal.
cw-lift₁-equiv : ∀ {n} (skel : Skeleton n)
  → ⟦ cw-lift₁ skel ⟧ ≃ ⟦ skel ⟧
cw-lift₁-equiv skel = equiv to incl to-incl incl-to
  where
    to : ⟦ cw-lift₁ skel ⟧ → ⟦ skel ⟧
    to = Attached-rec (idf ⟦ skel ⟧) (λ{(lift ())}) (λ{(lift ()) _})

    to-incl : ∀ x → to (incl x) == x
    to-incl _ = idp

    incl-to : ∀ x → incl (to x) == x
    incl-to = Attached-elim (λ _ → idp) (λ{(lift ())}) (λ{(lift ()) _})

cw-lift : ∀ {n m : ℕ} → n < m → Skeleton n → Skeleton m
cw-lift ltS = cw-lift₁
cw-lift (ltSR lt) = cw-lift₁ ∘ cw-lift lt
