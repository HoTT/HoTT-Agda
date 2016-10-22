{-# OPTIONS --without-K #-}

{-
  Adapted from Ulrik's work in Lean (released under Apache License 2.0)
  https://github.com/leanprover/lean/blob/master/hott/homotopy/cellcomplex.hlean
-}

open import HoTT
open import homotopy.DistinctlyPointedSet

module cw.CW {i} where

open import cw.Attached public

{-
  Naming convention: most of them have the "cw-" prefix
-}

-- skeleton
{-
  Disadvantages of alternative definitions:

  [Skeleton] as a data type: No η. ([Skeleton (S n)] does not expand.)
  [Skeleton] as a recursive record type: No η.
  [Skeleton] as a recursive function: [n] is not inferable from terms.

  The following is combines a recursive funcition and a non-recursive
  record type which should strike a good balance.
-}

record AttachedSkeleton n (Skel : Type (lsucc i)) (Real : Skel → Type i)
  : Type (lsucc i) where
  constructor attached-skeleton
  field
    skel : Skel
    cells : hSet i
    attaching : Attaching (Real skel) (fst cells) (Sphere n)

Skeleton : ℕ → Type (lsucc i)
Realizer : {n : ℕ} → Skeleton n → Type i

Skeleton O = hSet i
Skeleton (S n) = AttachedSkeleton n (Skeleton n) Realizer

Realizer {n = O} A = fst A
Realizer {n = S n} (attached-skeleton _ _ α) = Attached α

⟦_⟧ = Realizer

-- Pointedness

-- this function is needed for pointedness
cw-head : ∀ {n : ℕ} → Skeleton n → Type i
cw-head {n = O} cells = fst cells
cw-head {n = S n} (attached-skeleton skel _ _) = cw-head skel

-- this function is needed for pointedness
incl^ : ∀ {n : ℕ} (skel : Skeleton n)
  → cw-head skel → ⟦ skel ⟧
incl^ {n = O} cells a = a
incl^ {n = S n} (attached-skeleton skel _ _) a = incl (incl^ skel a)

record ⊙Skeleton (n : ℕ) : Type (lsucc i) where
  constructor ⊙skeleton
  field
    skel : Skeleton n
    pt : cw-head skel
    pt-dec : has-distinct-pt ⊙[ cw-head skel , pt ]

⊙Realizer : {n : ℕ} → ⊙Skeleton n → Ptd i
⊙Realizer (⊙skeleton skel pt _) = ⟦ skel ⟧ , incl^ skel pt

⊙⟦_⟧ = ⊙Realizer

-- Take a prefix of a skeleton

cw-init : ∀ {n} → Skeleton (S n) → Skeleton n
cw-init (attached-skeleton skel _ _) = skel

⊙cw-init : ∀ {n} → ⊙Skeleton (S n) → ⊙Skeleton n
⊙cw-init (⊙skeleton skel pt dec) = ⊙skeleton (cw-init skel) pt dec

cw-take : ∀ {m n : ℕ} (m≤n : m ≤ n) → Skeleton n → Skeleton m
cw-take (inl idp)        skel = skel
cw-take (inr ltS)        skel = cw-init skel
cw-take (inr (ltSR m≤n)) skel = cw-take (inr m≤n) (cw-init skel)

⊙cw-take : ∀ {m n : ℕ} (m≤n : m ≤ n) → ⊙Skeleton n → ⊙Skeleton m
⊙cw-take (inl idp)        ⊙skel = ⊙skel
⊙cw-take (inr ltS)        ⊙skel = ⊙cw-init ⊙skel
⊙cw-take (inr (ltSR m≤n)) ⊙skel = ⊙cw-take (inr m≤n) (⊙cw-init ⊙skel)

⊙cw-head : ∀ {n : ℕ} → ⊙Skeleton n → Ptd i
⊙cw-head (⊙skeleton skel pt _) = ⊙[ cw-head skel , pt ]

-- Access the [m]th cells

cells-last : ∀ {n : ℕ} → Skeleton n → Type i
cells-last {n = O} cells = fst cells
cells-last {n = S n} (attached-skeleton _ cells _) = fst cells

⊙cells-last : ∀ {n : ℕ} → ⊙Skeleton n → Type i
⊙cells-last (⊙skeleton skel _ _) = cells-last skel

cells-nth : ∀ {m n : ℕ} (m≤n : m ≤ n) → Skeleton n → Type i
cells-nth m≤n = cells-last ∘ cw-take m≤n

⊙cells-nth : ∀ {m n : ℕ} (m≤n : m ≤ n) → ⊙Skeleton n → Type i
⊙cells-nth m≤n = ⊙cells-last ∘ ⊙cw-take m≤n

-- Access the [m]th dimensional attaching map

Realizer₋₁ : ∀ {n : ℕ} → Skeleton (S n) → Type i
Realizer₋₁ = ⟦_⟧ ∘ cw-init

⟦_⟧₋₁ = Realizer₋₁

⊙Realizer₋₁ : ∀ {n : ℕ} → ⊙Skeleton (S n) → Ptd i
⊙Realizer₋₁ = ⊙⟦_⟧ ∘ ⊙cw-init

⊙⟦_⟧₋₁ = ⊙Realizer₋₁

attaching-last : ∀ {n : ℕ} (skel : Skeleton (S n))
  → cells-last skel → (Sphere n → ⟦ skel ⟧₋₁)
attaching-last (attached-skeleton _ _ attaching) = attaching

⊙attaching-last : ∀ {n : ℕ} (⊙skel : ⊙Skeleton (S n))
  → ⊙cells-last ⊙skel → (Sphere n → fst ⊙⟦ ⊙skel ⟧₋₁)
⊙attaching-last = attaching-last ∘ ⊙Skeleton.skel

attaching-nth : ∀ {m n : ℕ} (Sm≤n : S m ≤ n) (skel : Skeleton n)
  → cells-nth Sm≤n skel → (Sphere m → ⟦ cw-take Sm≤n skel ⟧₋₁)
attaching-nth Sm≤n = attaching-last ∘ cw-take Sm≤n

⊙attaching-nth : ∀ {m n : ℕ} (Sm≤n : S m ≤ n) (⊙skel : ⊙Skeleton n)
  → ⊙cells-nth Sm≤n ⊙skel → Sphere m → fst ⊙⟦ ⊙cw-take Sm≤n ⊙skel ⟧₋₁
⊙attaching-nth Sm≤n = ⊙attaching-last ∘ ⊙cw-take Sm≤n

-- Access the [m]th dimensional inclusion map

incl-last : ∀ {n} (skel : Skeleton (S n))
  → (⟦ skel ⟧₋₁ → ⟦ skel ⟧)
incl-last _ = incl

⊙incl-last : ∀ {n} (⊙skel : ⊙Skeleton (S n))
  → (⊙⟦ ⊙skel ⟧₋₁ ⊙→ ⊙⟦ ⊙skel ⟧)
⊙incl-last _ = incl , idp

incl-nth : ∀ {m n : ℕ} (Sm≤n : S m ≤ n) (skel : Skeleton n)
  → ⟦ cw-take Sm≤n skel ⟧₋₁ → ⟦ cw-take Sm≤n skel ⟧
incl-nth Sm≤n = incl-last ∘ cw-take Sm≤n

⊙incl-nth : ∀ {m n : ℕ} (Sm≤n : S m ≤ n) (⊙skel : ⊙Skeleton n)
  → (⊙⟦ ⊙cw-take Sm≤n ⊙skel ⟧₋₁ ⊙→ ⊙⟦ ⊙cw-take Sm≤n ⊙skel ⟧)
⊙incl-nth Sm≤n = ⊙incl-last ∘ ⊙cw-take Sm≤n

-- Extra conditions on CW complexes

-- 1. decidable equalities
has-cells-with-dec-eq : ∀ {n} → Skeleton n → Type i
has-cells-with-dec-eq {n = O} skel = has-dec-eq (cells-last skel)
has-cells-with-dec-eq {n = S n} skel =
  has-cells-with-dec-eq (cw-init skel) × has-dec-eq (cells-last skel)

has-cells-with-dec-eq-is-prop : ∀ {n} {skel : Skeleton n}
  → is-prop (has-cells-with-dec-eq skel)
has-cells-with-dec-eq-is-prop {n = O} = has-dec-eq-is-prop
has-cells-with-dec-eq-is-prop {n = S n} =
  ×-level has-cells-with-dec-eq-is-prop has-dec-eq-is-prop

-- 2. choice
has-cells-with-choice : (t : TLevel) {n : ℕ} (skel : Skeleton n)
  (j : ULevel) → Type (lmax i (lsucc j))
has-cells-with-choice t {n = O} skel j = has-choice t (cells-last skel) j
has-cells-with-choice t {n = S n} skel j =
  has-cells-with-choice t (cw-init skel) j × has-choice t (cells-last skel) j

{-
The following are unneeded.

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
-}
