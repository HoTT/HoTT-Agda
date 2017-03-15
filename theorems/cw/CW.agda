{-# OPTIONS --without-K --rewriting #-}

{-
  Adapted from Ulrik's work in Lean (released under Apache License 2.0)
  https://github.com/leanprover/lean/blob/master/hott/homotopy/cellcomplex.hlean
-}

open import HoTT renaming (pt to pt⊙)
open import homotopy.DisjointlyPointedSet

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
  [Skeleton] as a recursive fuction giving recursive Σ types:
    need to specify [n] in many places.

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

-- disjointly pointed skeletons
record ⊙Skeleton (n : ℕ) : Type (lsucc i) where
  constructor ⊙skeleton
  field
    skel : Skeleton n
    pt : cw-head skel
    pt-dec : is-separable ⊙[ cw-head skel , pt ]

⊙Realizer : {n : ℕ} → ⊙Skeleton n → Ptd i
⊙Realizer (⊙skeleton skel pt _) = ⊙[ ⟦ skel ⟧ , incl^ skel pt ]

⊙⟦_⟧ = ⊙Realizer

-- Take a prefix of a skeleton

cw-init : ∀ {n} → Skeleton (S n) → Skeleton n
cw-init (attached-skeleton skel _ _) = skel

⊙cw-init : ∀ {n} → ⊙Skeleton (S n) → ⊙Skeleton n
⊙cw-init (⊙skeleton skel pt dec) = ⊙skeleton (cw-init skel) pt dec

cw-take : ∀ {m n : ℕ} (m≤n : m ≤ n) → Skeleton n → Skeleton m
cw-take (inl idp)        skel = skel
cw-take (inr ltS)        skel = cw-init skel
cw-take (inr (ltSR m<n)) skel = cw-take (inr m<n) (cw-init skel)

cw-init-take : ∀ {m n : ℕ} (Sm≤n : S m ≤ n) skel
  → cw-init (cw-take Sm≤n skel) == cw-take (≤-trans lteS Sm≤n) skel
cw-init-take (inl idp) skel = idp
cw-init-take (inr ltS) skel = idp
cw-init-take (inr (ltSR lt)) skel = cw-init-take (inr lt) (cw-init skel)

⊙cw-take : ∀ {m n : ℕ} (m≤n : m ≤ n) → ⊙Skeleton n → ⊙Skeleton m
⊙cw-take (inl idp)        ⊙skel = ⊙skel
⊙cw-take (inr ltS)        ⊙skel = ⊙cw-init ⊙skel
⊙cw-take (inr (ltSR m<n)) ⊙skel = ⊙cw-take (inr m<n) (⊙cw-init ⊙skel)

⊙cw-head : ∀ {n : ℕ} → ⊙Skeleton n → Ptd i
⊙cw-head (⊙skeleton skel pt _) = ⊙[ cw-head skel , pt ]

⊙cw-init-take : ∀ {m n : ℕ} (Sm≤n : S m ≤ n) ⊙skel
  → ⊙cw-init (⊙cw-take Sm≤n ⊙skel) == ⊙cw-take (≤-trans lteS Sm≤n) ⊙skel
⊙cw-init-take (inl idp) ⊙skel = idp
⊙cw-init-take (inr ltS) ⊙skel = idp
⊙cw-init-take (inr (ltSR lt)) ⊙skel = ⊙cw-init-take (inr lt) (⊙cw-init ⊙skel)

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
  → ⊙cells-last ⊙skel → (Sphere n → de⊙ ⊙⟦ ⊙skel ⟧₋₁)
⊙attaching-last = attaching-last ∘ ⊙Skeleton.skel

attaching-nth : ∀ {m n : ℕ} (Sm≤n : S m ≤ n) (skel : Skeleton n)
  → cells-nth Sm≤n skel → (Sphere m → ⟦ cw-take Sm≤n skel ⟧₋₁)
attaching-nth Sm≤n = attaching-last ∘ cw-take Sm≤n

⊙attaching-nth : ∀ {m n : ℕ} (Sm≤n : S m ≤ n) (⊙skel : ⊙Skeleton n)
  → ⊙cells-nth Sm≤n ⊙skel → Sphere m → de⊙ ⊙⟦ ⊙cw-take Sm≤n ⊙skel ⟧₋₁
⊙attaching-nth Sm≤n = ⊙attaching-last ∘ ⊙cw-take Sm≤n

-- Access the [m]th dimensional inclusion map

cw-incl-last : ∀ {n} (skel : Skeleton (S n))
  → (⟦ skel ⟧₋₁ → ⟦ skel ⟧)
cw-incl-last _ = incl

⊙cw-incl-last : ∀ {n} (⊙skel : ⊙Skeleton (S n))
  → (⊙⟦ ⊙skel ⟧₋₁ ⊙→ ⊙⟦ ⊙skel ⟧)
⊙cw-incl-last _ = incl , idp

cw-incl-nth : ∀ {m n : ℕ} (Sm≤n : S m ≤ n) (skel : Skeleton n)
  → ⟦ cw-take Sm≤n skel ⟧₋₁ → ⟦ cw-take Sm≤n skel ⟧
cw-incl-nth Sm≤n = cw-incl-last ∘ cw-take Sm≤n

⊙cw-incl-nth : ∀ {m n : ℕ} (Sm≤n : S m ≤ n) (⊙skel : ⊙Skeleton n)
  → (⊙⟦ ⊙cw-take Sm≤n ⊙skel ⟧₋₁ ⊙→ ⊙⟦ ⊙cw-take Sm≤n ⊙skel ⟧)
⊙cw-incl-nth Sm≤n = ⊙cw-incl-last ∘ ⊙cw-take Sm≤n

cw-incl-tail : ∀ {m n : ℕ} (m≤n : m ≤ n) (skel : Skeleton n)
  → (⟦ cw-take m≤n skel ⟧ → ⟦ skel ⟧)
cw-incl-tail (inl idp) skel = idf ⟦ skel ⟧
cw-incl-tail (inr ltS) skel = cw-incl-last skel
cw-incl-tail (inr (ltSR lt)) skel =
  cw-incl-last skel ∘ cw-incl-tail (inr lt) (cw-init skel)

⊙cw-incl-tail : ∀ {m n : ℕ} (m≤n : m ≤ n) (⊙skel : ⊙Skeleton n)
  → (⊙⟦ ⊙cw-take m≤n ⊙skel ⟧ ⊙→ ⊙⟦ ⊙skel ⟧)
⊙cw-incl-tail (inl idp) ⊙skel = ⊙idf ⊙⟦ ⊙skel ⟧
⊙cw-incl-tail (inr ltS) ⊙skel = ⊙cw-incl-last ⊙skel
⊙cw-incl-tail (inr (ltSR lt)) ⊙skel =
  ⊙cw-incl-last ⊙skel ⊙∘ ⊙cw-incl-tail (inr lt) (⊙cw-init ⊙skel)

-- Extra conditions on CW complexes

-- 1. decidable equalities
has-cells-with-dec-eq : ∀ {n} → Skeleton n → Type i
has-cells-with-dec-eq {n = O} skel = has-dec-eq (cells-last skel)
has-cells-with-dec-eq {n = S n} skel =
  has-cells-with-dec-eq (cw-init skel) × has-dec-eq (cells-last skel)

⊙has-cells-with-dec-eq : ∀ {n} → ⊙Skeleton n → Type i
⊙has-cells-with-dec-eq = has-cells-with-dec-eq ∘ ⊙Skeleton.skel

cells-last-has-dec-eq : ∀ {n} (skel : Skeleton n)
  → has-cells-with-dec-eq skel → has-dec-eq (cells-last skel)
cells-last-has-dec-eq {n = O} skel dec = dec
cells-last-has-dec-eq {n = S n} skel dec = snd dec

init-has-cells-with-dec-eq : ∀ {n} (skel : Skeleton (S n))
  → has-cells-with-dec-eq skel
  → has-cells-with-dec-eq (cw-init skel)
init-has-cells-with-dec-eq skel dec = fst dec

take-has-cells-with-dec-eq : ∀ {m n} (m≤n : m ≤ n) (skel : Skeleton n)
  → has-cells-with-dec-eq skel
  → has-cells-with-dec-eq (cw-take m≤n skel)
take-has-cells-with-dec-eq (inl idp) skel dec = dec
take-has-cells-with-dec-eq (inr ltS) skel dec = init-has-cells-with-dec-eq skel dec
take-has-cells-with-dec-eq (inr (ltSR lt)) skel dec
  = take-has-cells-with-dec-eq (inr lt) (cw-init skel) (init-has-cells-with-dec-eq skel dec)

cells-nth-has-dec-eq : ∀ {m n} (m≤n : m ≤ n) (skel : Skeleton n)
  → has-cells-with-dec-eq skel → has-dec-eq (cells-nth m≤n skel)
cells-nth-has-dec-eq m≤n skel dec =
  cells-last-has-dec-eq (cw-take m≤n skel)
    (take-has-cells-with-dec-eq m≤n skel dec)

has-cells-with-dec-eq-is-prop : ∀ {n} {skel : Skeleton n}
  → is-prop (has-cells-with-dec-eq skel)
has-cells-with-dec-eq-is-prop {n = O} = has-dec-eq-is-prop
has-cells-with-dec-eq-is-prop {n = S n} =
  ×-level has-cells-with-dec-eq-is-prop has-dec-eq-is-prop

-- 2. choice
has-cells-with-choice : TLevel → {n : ℕ} → Skeleton n → (j : ULevel) → Type (lmax i (lsucc j))
has-cells-with-choice t {n = O} skel j = has-choice t (cells-last skel) j
has-cells-with-choice t {n = S n} skel j =
  has-cells-with-choice t (cw-init skel) j × has-choice t (cells-last skel) j

⊙has-cells-with-choice : TLevel → {n : ℕ} → ⊙Skeleton n → (j : ULevel) → Type (lmax i (lsucc j))
⊙has-cells-with-choice t ⊙skel j = has-cells-with-choice t (⊙Skeleton.skel ⊙skel) j

⊙cells-last-has-choice : {t : TLevel} {n : ℕ} (⊙skel : ⊙Skeleton n) {j : ULevel}
  → ⊙has-cells-with-choice t ⊙skel j
  → has-choice t (⊙cells-last ⊙skel) j
⊙cells-last-has-choice {n = O} ⊙skel ac = ac
⊙cells-last-has-choice {n = S n} ⊙skel ac = snd ac

⊙init-has-cells-with-choice : {t : TLevel} {n : ℕ} (⊙skel : ⊙Skeleton (S n)) {j : ULevel}
  → ⊙has-cells-with-choice t ⊙skel j
  → ⊙has-cells-with-choice t (⊙cw-init ⊙skel) j
⊙init-has-cells-with-choice ⊙skel ac = fst ac

⊙take-has-cells-with-choice : {t : TLevel} {m n : ℕ} (m≤n : m ≤ n) (⊙skel : ⊙Skeleton n) {j : ULevel}
  → ⊙has-cells-with-choice t ⊙skel j
  → ⊙has-cells-with-choice t (⊙cw-take m≤n ⊙skel) j
⊙take-has-cells-with-choice (inl idp) ⊙skel ac = ac
⊙take-has-cells-with-choice (inr ltS) ⊙skel ac = ⊙init-has-cells-with-choice ⊙skel ac
⊙take-has-cells-with-choice (inr (ltSR lt)) ⊙skel ac
  = ⊙take-has-cells-with-choice (inr lt) (⊙cw-init ⊙skel) (⊙init-has-cells-with-choice ⊙skel ac)

⊙cells-nth-has-choice : {t : TLevel} {m n : ℕ} (m≤n : m ≤ n) (⊙skel : ⊙Skeleton n) {j : ULevel}
  → ⊙has-cells-with-choice t ⊙skel j
  → has-choice t (⊙cells-nth m≤n ⊙skel) j
⊙cells-nth-has-choice m≤n ⊙skel ac = ⊙cells-last-has-choice (⊙cw-take m≤n ⊙skel)
  (⊙take-has-cells-with-choice m≤n ⊙skel ac)

{-
The following are not needed.

-- Dimensional lifting

cw-lift₁ : ∀ {n : ℕ} → Skeleton n → Skeleton (S n)
cw-lift₁ skel = attached-skeleton skel
  (Lift Empty , Lift-level Empty-is-set)
  λ{(lift ()) _}

-- This slightly stretches the naming convension
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
