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

⦉_⦊ = FinSkeleton-realize

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
  → fcw-head skel → ⟦ ⦉ skel ⦊ ⟧
fcw-incl^ fin-skel = incl^ (FinSkeleton-realize fin-skel)

-- disjointly pointed skeletons
record ⊙FinSkeleton (n : ℕ) : Type₁ where
  constructor ⊙fin-skeleton
  field
    skel : FinSkeleton n
    pt : fcw-head skel

⊙FinSkeleton-realize : {n : ℕ} → ⊙FinSkeleton n → ⊙Skeleton {i = lzero} n
⊙FinSkeleton-realize (⊙fin-skeleton skel pt) =
  ⊙skeleton (FinSkeleton-realize skel) pt (fcw-head-has-dec-eq skel pt)

⊙⦉_⦊ : {n : ℕ} → ⊙FinSkeleton n → ⊙Skeleton {i = lzero} n
⊙⦉_⦊ = ⊙FinSkeleton-realize

-- Take a prefix of a skeleton

fcw-init : ∀ {n} → FinSkeleton (S n) → FinSkeleton n
fcw-init (attached-fin-skeleton skel _ _) = skel

⊙fcw-init : ∀ {n} → ⊙FinSkeleton (S n) → ⊙FinSkeleton n
⊙fcw-init (⊙fin-skeleton skel pt) = ⊙fin-skeleton (fcw-init skel) pt

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
