{-# OPTIONS --without-K --rewriting #-}

open import HoTT renaming (pt to pt⊙)
open import cw.CW

module cw.FinCW where

record AttachedFinSkeleton n (Skel : Type₀) (Real : Skel → Skeleton n) : Type₀ where
  constructor attached-fin-skeleton
  field
    skel : Skel
    numCells : ℕ
    attaching : Attaching ⟦ Real skel ⟧ (Fin numCells) (Sphere n)

FinSkeleton : ℕ → Type₀
FinSkeleton-realize : {n : ℕ} → FinSkeleton n → Skeleton n

FinSkeleton O = ℕ
FinSkeleton (S n) = AttachedFinSkeleton n (FinSkeleton n) FinSkeleton-realize

FinSkeleton-realize {n = O} n = Fin n , Fin-is-set
FinSkeleton-realize {n = S n} (attached-fin-skeleton _ s α) =
  attached-skeleton _ (Fin s , Fin-is-set) α

f⟦_⟧ : {n : ℕ} → FinSkeleton n → Type₀
f⟦_⟧ = Realizer ∘ FinSkeleton-realize

-- Pointedness

-- this function is needed for pointedness
fcw-head : ∀ {n : ℕ} → FinSkeleton n → Type₀
fcw-head = cw-head ∘ FinSkeleton-realize

fcw-head-has-dec-eq : ∀ {n : ℕ} (fin-skel : FinSkeleton n)
  → has-dec-eq (fcw-head fin-skel)
fcw-head-has-dec-eq {n = 0} _ = Fin-has-dec-eq
fcw-head-has-dec-eq {n = S n} (attached-fin-skeleton skel _ _) =
  fcw-head-has-dec-eq skel

-- this function is needed for pointedness
fcw-incl^ : ∀ {n : ℕ} (skel : FinSkeleton n)
  → fcw-head skel → f⟦ skel ⟧
fcw-incl^ fin-skel = incl^ (FinSkeleton-realize fin-skel)

-- disjointly pointed skeletons
record ⊙FinSkeleton (n : ℕ) : Type₁ where
  constructor ⊙fin-skeleton
  field
    skel : FinSkeleton n
    pt : fcw-head skel

⊙FinSkeleton-realize : {n : ℕ} → ⊙FinSkeleton n → ⊙Skeleton n
⊙FinSkeleton-realize (⊙fin-skeleton skel pt) =
  ⊙skeleton (FinSkeleton-realize skel) pt (fcw-head-has-dec-eq skel pt)

⊙FinRealizer : {n : ℕ} → ⊙FinSkeleton n → Ptd₀
⊙FinRealizer = ⊙Realizer ∘ ⊙FinSkeleton-realize

⊙f⟦_⟧ = ⊙FinRealizer

-- Take a prefix of a skeleton

fcw-init : ∀ {n} → FinSkeleton (S n) → FinSkeleton n
fcw-init (attached-fin-skeleton skel _ _) = skel

⊙fcw-init : ∀ {n} → ⊙FinSkeleton (S n) → ⊙FinSkeleton n
⊙fcw-init (⊙fin-skeleton skel pt) = ⊙fin-skeleton (fcw-init skel) pt

{-
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

-}

-- Extra conditions on CW complexes

-- 1. decidable equalities
FinSkeleton-has-cells-with-dec-eq : ∀ {n} (fin-skel : FinSkeleton n)
  → has-cells-with-dec-eq (FinSkeleton-realize fin-skel)
FinSkeleton-has-cells-with-dec-eq {n = O} fin-skel = Fin-has-dec-eq
FinSkeleton-has-cells-with-dec-eq {n = S n} fin-skel =
  FinSkeleton-has-cells-with-dec-eq (fcw-init fin-skel) , Fin-has-dec-eq

⊙FinSkeleton-has-cells-with-dec-eq : ∀ {n} (⊙fin-skel : ⊙FinSkeleton n)
  → ⊙has-cells-with-dec-eq (⊙FinSkeleton-realize ⊙fin-skel)
⊙FinSkeleton-has-cells-with-dec-eq ⊙fin-skel = FinSkeleton-has-cells-with-dec-eq _

-- 2. choice

FinSkeleton-has-cells-with-choice : ∀ t {n} (fin-skel : FinSkeleton n) j
  → has-cells-with-choice t (FinSkeleton-realize fin-skel) j
FinSkeleton-has-cells-with-choice t {n = O} fin-skel j = Fin-has-choice t j
FinSkeleton-has-cells-with-choice t {n = S n} fin-skel j =
  FinSkeleton-has-cells-with-choice t (fcw-init fin-skel) j , Fin-has-choice t j

⊙FinSkeleton-has-cells-with-choice : ∀ t {n} (fin-skel : ⊙FinSkeleton n) j
  → ⊙has-cells-with-choice t (⊙FinSkeleton-realize fin-skel) j
⊙FinSkeleton-has-cells-with-choice t fin-skel j = FinSkeleton-has-cells-with-choice t _ j
