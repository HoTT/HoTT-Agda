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
Skeleton {i} (S n) =
  Σ (Skeleton {i} n)
    (λ s → Σ (Type i) λ A → Boundry (Realizer s) A (Sphere {i} n))

Realizer {n = O} A = A
Realizer {n = S n} (s , (A , boundary)) = Attach boundary

⟦_⟧ = Realizer

-- Take a prefix of a skeleton

cw-take : ∀ {i} {m n : ℕ} (m≤n : m ≤ n) → Skeleton {i} n → Skeleton {i} m
cw-take (inl idp)        skel       = skel
cw-take (inr ltS)        (skel , _) = skel
cw-take (inr (ltSR m≤n)) (skel , _) = cw-take (inr m≤n) skel

cw-head : ∀ {i} {n : ℕ} → Skeleton {i} n → Type i
cw-head {n = O}   = cw-take (inl idp)
cw-head {n = S n} = cw-take (inr (O<S n))

incl^ : ∀ {i} {n : ℕ} (skel : Skeleton {i} n)
  → cw-head skel → ⟦ skel ⟧
incl^ {n = O}       skel       c = c
incl^ {n = S O}     (skel , _) c = incl c
incl^ {n = S (S n)} (skel , _) c = incl (incl^ skel c)

-- Pointedness

⊙Skeleton : ∀ {i} (n : ℕ) → Type (lsucc i)
⊙Skeleton n = Σ (Skeleton n) cw-head

⊙Realizer : ∀ {i} {n : ℕ} → ⊙Skeleton {i} n → Ptd i
⊙Realizer (skel , pt) = (⟦ skel ⟧ , incl^ skel pt)

⊙⟦_⟧ = ⊙Realizer

-- Access the [m]th cells

cw-cells-top : ∀ {i} {n : ℕ} → Skeleton {i} n → Type i
cw-cells-top {n = O}   skel            = skel
cw-cells-top {n = S n} (_ , cells , _) = cells

cw-cells : ∀ {i} {m n : ℕ} (m≤n : m ≤ n) → Skeleton {i} n → Type i
cw-cells m≤n = cw-cells-top ∘ cw-take m≤n

-- Access the [m]th boundary map

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

cw-boundary : ∀ {i} {m n : ℕ} (m≤n : m ≤ n) (skel : Skeleton {i} n)
  → cw-cells m≤n skel → Sphere₋₁ m → ⟦ cw-take m≤n skel ⟧₋₁
cw-boundary m≤n = cw-boundary-top ∘ cw-take m≤n

-- Misc

-- Extra conditions on CW complexes
-- XXX Needs a better name
has-dec-eq-cells : ∀ {i} {n} → Skeleton {i} n → Type i
has-dec-eq-cells {n = n} skel = ∀ {m} (m≤n : m ≤ n) → has-dec-eq (cw-cells m≤n skel)

{- Some basic CWs -}

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

{- Basic transformation  -}

-- dimension lifting

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
