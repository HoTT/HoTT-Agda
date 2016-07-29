{-# OPTIONS --without-K #-}

{-
  Adapted from Ulrik's work in Lean (released under Apache License 2.0)
  https://github.com/leanprover/lean/blob/master/hott/homotopy/cellcomplex.hlean
-}

open import HoTT

module cw.CW where

open import cw.Attach public

{-
  Naming convension: most of them have the "cw-" prefix
-}

-- skeleton

Skeleton : ∀ {i} → ℕ → Type (lsucc i)
Realizer : ∀ {i} {n : ℕ} → Skeleton {i} n → Type i

Skeleton {i} O = Type i
Skeleton {i} (S n) =
  Σ (Skeleton {i} n)
    (λ s → Σ (Type i) λ A → Boundry (Realizer s) A (Sphere n))

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

cells-last : ∀ {i} {n : ℕ} → Skeleton {i} n → Type i
cells-last {n = O}   skel            = skel
cells-last {n = S n} (_ , cells , _) = cells

cells-at : ∀ {i} {m n : ℕ} (m≤n : m ≤ n) → Skeleton {i} n → Type i
cells-at m≤n = cells-last ∘ cw-take m≤n

-- Access the [m]th boundary map

Sphere₋₁ : ℕ → Type₀
Sphere₋₁ O = Empty
Sphere₋₁ (S n) = Sphere n

Realizer₋₁ : ∀ {i} {n : ℕ} → Skeleton {i} n → Type i
Realizer₋₁ {n = O}   _          = Lift Empty
Realizer₋₁ {n = S n} (skel , _) = ⟦ skel ⟧

⟦_⟧₋₁ = Realizer₋₁

boundary-last : ∀ {i} {n : ℕ} (s : Skeleton {i} n)
  → cells-last s → (Sphere₋₁ n → ⟦ s ⟧₋₁)
boundary-last {n = O}    _                 = λ{_ ()}
boundary-last {n = S n} (_ , _ , boundary) = boundary

boundary-at : ∀ {i} {m n : ℕ} (m≤n : m ≤ n) (skel : Skeleton {i} n)
  → cells-at m≤n skel → Sphere₋₁ m → ⟦ cw-take m≤n skel ⟧₋₁
boundary-at m≤n = boundary-last ∘ cw-take m≤n

-- Misc

-- Extra conditions on CW complexes
-- XXX Needs a better name
has-dec-cells : ∀ {i} {n} → Skeleton {i} n → Type i
has-dec-cells {n = 0} skel = has-dec-eq skel
has-dec-cells {n = S n} (skel , cells , _) = has-dec-cells skel × has-dec-eq cells

-- Extra conditions on CW complexes for constructive degrees
-- The ideas is that boundaries maps need to be pointed after contraction
-- XXX Needs a better name
is-aligned : ∀ {i} {n} → Skeleton {i} n → Type i
is-aligned {n = 0} _ = Lift ⊤
is-aligned {n = 1} _ = Lift ⊤
is-aligned {n = S (S n)} (skel , _ , boundary) =
  is-aligned skel × (∀ c → hfiber incl (boundary c north))

{- Some basic CWs -}

-- Empty

CWEmpty-skel : Skeleton {lzero} 0
CWEmpty-skel = Empty
CWEmpty = ⟦ CWEmpty-skel ⟧

CWEmpty≃Empty : CWEmpty ≃ Empty
CWEmpty≃Empty = ide _

CWEmpty-is-aligned : is-aligned CWEmpty-skel
CWEmpty-is-aligned = lift tt

-- Unit

CWUnit-skel : Skeleton {lzero} 0
CWUnit-skel = Unit
CWUnit = ⟦ CWUnit-skel ⟧

CWUnit≃Unit : CWUnit ≃ Unit
CWUnit≃Unit = ide _

CWUnit-is-aligned : is-aligned CWUnit-skel
CWUnit-is-aligned = lift tt

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
