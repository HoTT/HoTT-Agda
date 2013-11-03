{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Nat
open import lib.types.Group

module lib.types.Int where

data ℤ : Type₀ where
  O : ℤ
  pos : (n : ℕ) → ℤ
  neg : (n : ℕ) → ℤ

Int = ℤ

succ : ℤ → ℤ
succ O = pos O
succ (pos n) = pos (S n)
succ (neg O) = O
succ (neg (S n)) = neg n

pred : ℤ → ℤ
pred O = neg O
pred (pos O) = O
pred (pos (S n)) = pos n
pred (neg n) = neg (S n)

abstract
  succ-pred : (n : ℤ) → succ (pred n) == n
  succ-pred O = idp
  succ-pred (pos O) = idp
  succ-pred (pos (S n)) = idp
  succ-pred (neg n) = idp

  pred-succ : (n : ℤ) → pred (succ n) == n
  pred-succ O = idp
  pred-succ (pos n) = idp
  pred-succ (neg O) = idp
  pred-succ (neg (S n)) = idp

succ-equiv : ℤ ≃ ℤ
succ-equiv = equiv succ pred succ-pred pred-succ

{- Proof that [ℤ] has decidable equality and hence is a set -}

private
  ℤ-get-pos : ℤ → ℕ
  ℤ-get-pos O = 0
  ℤ-get-pos (pos n) = n
  ℤ-get-pos (neg n) = 0

  pos-injective : (n m : ℕ) (p : pos n == pos m) → n == m
  pos-injective n m p = ap ℤ-get-pos p

  ℤ-get-neg : ℤ → ℕ
  ℤ-get-neg O = 0
  ℤ-get-neg (pos n) = 0
  ℤ-get-neg (neg n) = n

  neg-injective : (n m : ℕ) (p : neg n == neg m) → n == m
  neg-injective n m p = ap ℤ-get-neg p

  ℤ-neg≠O≠pos-type : ℤ → Type₀
  ℤ-neg≠O≠pos-type O = Unit
  ℤ-neg≠O≠pos-type (pos n) = Empty
  ℤ-neg≠O≠pos-type (neg n) = Empty

  ℤ-neg≠pos-type : ℤ → Type₀
  ℤ-neg≠pos-type O = Unit
  ℤ-neg≠pos-type (pos n) = Empty
  ℤ-neg≠pos-type (neg n) = Unit

abstract
  ℤ-O≠pos : (n : ℕ) → O ≠ pos n
  ℤ-O≠pos n p = transport ℤ-neg≠O≠pos-type p unit

  ℤ-pos≠O : (n : ℕ) → pos n ≠ O
  ℤ-pos≠O n p = transport ℤ-neg≠O≠pos-type (! p) unit

  ℤ-O≠neg : (n : ℕ) → O ≠ neg n
  ℤ-O≠neg n p = transport ℤ-neg≠O≠pos-type p unit

  ℤ-neg≠O : (n : ℕ) → neg n ≠ O
  ℤ-neg≠O n p = transport ℤ-neg≠O≠pos-type (! p) unit

  ℤ-neg≠pos : (n m : ℕ) → neg n ≠ pos m
  ℤ-neg≠pos n m p = transport ℤ-neg≠pos-type p unit

  ℤ-pos≠neg : (n m : ℕ) → pos n ≠ neg m
  ℤ-pos≠neg n m p = transport ℤ-neg≠pos-type (! p) unit

  ℤ-has-dec-eq : has-dec-eq ℤ
  ℤ-has-dec-eq O O = inl idp
  ℤ-has-dec-eq O (pos n) = inr (ℤ-O≠pos n)
  ℤ-has-dec-eq O (neg n) = inr (ℤ-O≠neg n)
  ℤ-has-dec-eq (pos n) O = inr (ℤ-pos≠O n)
  ℤ-has-dec-eq (pos n) (pos m) with ℕ-has-dec-eq n m
  ℤ-has-dec-eq (pos n) (pos m) | inl p = inl (ap pos p)
  ℤ-has-dec-eq (pos n) (pos m) | inr p⊥ = inr (λ p → p⊥ (pos-injective n m p))
  ℤ-has-dec-eq (pos n) (neg m) = inr (ℤ-pos≠neg n m)
  ℤ-has-dec-eq (neg n) O = inr (ℤ-neg≠O n)
  ℤ-has-dec-eq (neg n) (pos m) = inr (ℤ-neg≠pos n m)
  ℤ-has-dec-eq (neg n) (neg m) with ℕ-has-dec-eq n m
  ℤ-has-dec-eq (neg n) (neg m) | inl p = inl (ap neg p)
  ℤ-has-dec-eq (neg n) (neg m) | inr p⊥ = inr (λ p → p⊥ (neg-injective n m p))

  ℤ-is-set : is-set ℤ
  ℤ-is-set = dec-eq-is-set ℤ-has-dec-eq

ℤ-level = ℤ-is-set

{-
  ℤ is also a group!
-}

-- inv
ℤ~ : ℤ → ℤ
ℤ~ O = O
ℤ~ (pos n) = neg n
ℤ~ (neg n) = pos n

-- comp
_ℤ+_ : ℤ → ℤ → ℤ
O         ℤ+ z = z
pos O     ℤ+ z = succ z
pos (S n) ℤ+ z = succ (pos n ℤ+ z)
neg O     ℤ+ z = pred z
neg (S n) ℤ+ z = pred (neg n ℤ+ z)

-- unit-l
ℤ+-unit-l : ∀ z → O ℤ+ z == z
ℤ+-unit-l _ = idp

-- unit-r
private
  ℤ+-unit-r-pos : ∀ n → pos n ℤ+ O == pos n
  ℤ+-unit-r-pos O     = idp
  ℤ+-unit-r-pos (S n) = ap succ $ ℤ+-unit-r-pos n

  ℤ+-unit-r-neg : ∀ n → neg n ℤ+ O == neg n
  ℤ+-unit-r-neg O     = idp
  ℤ+-unit-r-neg (S n) = ap pred $ ℤ+-unit-r-neg n

ℤ+-unit-r : ∀ z → z ℤ+ O == z
ℤ+-unit-r O = idp
ℤ+-unit-r (pos n) = ℤ+-unit-r-pos n
ℤ+-unit-r (neg n) = ℤ+-unit-r-neg n

-- assoc
succ-ℤ+ : ∀ z₁ z₂ → succ z₁ ℤ+ z₂ == succ (z₁ ℤ+ z₂)
succ-ℤ+ O _ = idp
succ-ℤ+ (pos n) _ = idp
succ-ℤ+ (neg O) _ = ! $ succ-pred _
succ-ℤ+ (neg (S n)) _ = ! $ succ-pred _

pred-ℤ+ : ∀ z₁ z₂ → pred z₁ ℤ+ z₂ == pred (z₁ ℤ+ z₂)
pred-ℤ+ O _ = idp
pred-ℤ+ (neg n) _ = idp
pred-ℤ+ (pos O) _ = ! $ pred-succ _
pred-ℤ+ (pos (S n)) _ = ! $ pred-succ _

private
  ℤ+-assoc-pos : ∀ n₁ z₂ z₃ → (pos n₁ ℤ+ z₂) ℤ+ z₃ == pos n₁ ℤ+ (z₂ ℤ+ z₃)
  ℤ+-assoc-pos O      z₂ z₃ = succ-ℤ+ z₂ z₃
  ℤ+-assoc-pos (S n₁) z₂ z₃ =
    succ (pos n₁ ℤ+ z₂) ℤ+ z₃     =⟨ succ-ℤ+ (pos n₁ ℤ+ z₂) z₃ ⟩
    succ ((pos n₁ ℤ+ z₂) ℤ+ z₃)   =⟨ ap succ $ ℤ+-assoc-pos n₁ z₂ z₃ ⟩
    succ (pos n₁ ℤ+ (z₂ ℤ+ z₃))   ∎

  ℤ+-assoc-neg : ∀ n₁ z₂ z₃ → (neg n₁ ℤ+ z₂) ℤ+ z₃ == neg n₁ ℤ+ (z₂ ℤ+ z₃)
  ℤ+-assoc-neg O      z₂ z₃ = pred-ℤ+ z₂ z₃
  ℤ+-assoc-neg (S n₁) z₂ z₃ =
    pred (neg n₁ ℤ+ z₂) ℤ+ z₃     =⟨ pred-ℤ+ (neg n₁ ℤ+ z₂) z₃ ⟩
    pred ((neg n₁ ℤ+ z₂) ℤ+ z₃)   =⟨ ap pred $ ℤ+-assoc-neg n₁ z₂ z₃ ⟩
    pred (neg n₁ ℤ+ (z₂ ℤ+ z₃))   ∎

ℤ+-assoc : ∀ z₁ z₂ z₃ → (z₁ ℤ+ z₂) ℤ+ z₃ == z₁ ℤ+ (z₂ ℤ+ z₃)
ℤ+-assoc O        _ _ = idp
ℤ+-assoc (pos n₁) _ _ = ℤ+-assoc-pos n₁ _ _
ℤ+-assoc (neg n₁) _ _ = ℤ+-assoc-neg n₁ _ _

private
  pos-S-ℤ+-neg-S : ∀ n₁ n₂ → pos (S n₁) ℤ+ neg (S n₂) == pos n₁ ℤ+ neg n₂
  pos-S-ℤ+-neg-S O      n₂ = idp
  pos-S-ℤ+-neg-S (S n₁) n₂ = ap succ $ pos-S-ℤ+-neg-S n₁ n₂

  neg-S-ℤ+-pos-S : ∀ n₁ n₂ → neg (S n₁) ℤ+ pos (S n₂) == neg n₁ ℤ+ pos n₂
  neg-S-ℤ+-pos-S O      n₂ = idp
  neg-S-ℤ+-pos-S (S n₁) n₂ = ap pred $ neg-S-ℤ+-pos-S n₁ n₂

  ℤ~-inv-r-pos : ∀ n → pos n ℤ+ neg n == O
  ℤ~-inv-r-pos O     = idp
  ℤ~-inv-r-pos (S n) =
    pos (S n) ℤ+ neg (S n)  =⟨ pos-S-ℤ+-neg-S n n ⟩
    pos n ℤ+ neg n          =⟨ ℤ~-inv-r-pos n ⟩
    O                       ∎

  ℤ~-inv-r-neg : ∀ n → neg n ℤ+ pos n == O
  ℤ~-inv-r-neg O     = idp
  ℤ~-inv-r-neg (S n) =
    neg (S n) ℤ+ pos (S n)  =⟨ neg-S-ℤ+-pos-S n n ⟩
    neg n ℤ+ pos n          =⟨ ℤ~-inv-r-neg n ⟩
    O                       ∎

ℤ~-inv-r : ∀ z → z ℤ+ ℤ~ z == O
ℤ~-inv-r O       = idp
ℤ~-inv-r (pos n) = ℤ~-inv-r-pos n
ℤ~-inv-r (neg n) = ℤ~-inv-r-neg n

ℤ~-inv-l : ∀ z → ℤ~ z ℤ+ z == O
ℤ~-inv-l O       = idp
ℤ~-inv-l (pos n) = ℤ~-inv-r-neg n
ℤ~-inv-l (neg n) = ℤ~-inv-r-pos n

ℤ-group-structure : GroupStructure ℤ 
ℤ-group-structure = record
  { ident = O
  ; inv = ℤ~
  ; comp = _ℤ+_
  ; unitl = ℤ+-unit-l
  ; unitr = ℤ+-unit-r
  ; assoc = ℤ+-assoc
  ; invr = ℤ~-inv-r
  ; invl = ℤ~-inv-l
  }

ℤ-group : Group₀
ℤ-group = group _ ℤ-is-set ℤ-group-structure