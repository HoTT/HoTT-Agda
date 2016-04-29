{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Nat
open import lib.types.Group
open import lib.types.TLevel

module lib.types.Int where

data ℤ : Type₀ where
  pos : (n : ℕ) → ℤ
  negsucc : (n : ℕ) → ℤ

Int = ℤ

{-# BUILTIN INTEGER Int #-}
{-# BUILTIN INTEGERPOS pos #-}
{-# BUILTIN INTEGERNEGSUC negsucc #-}

{- literal overloading -}

instance
  ℤ-reader : FromNat ℤ
  FromNat.in-range ℤ-reader _ = ⊤
  FromNat.read ℤ-reader n = pos n

  ℤ-neg-reader : FromNeg ℤ
  FromNeg.in-range ℤ-neg-reader _ = ⊤
  FromNeg.read ℤ-neg-reader O = pos O
  FromNeg.read ℤ-neg-reader (S n) = negsucc n

{- succ and pred -}

succ : ℤ → ℤ
succ (pos n) = pos (S n)
succ (negsucc O) = pos O
succ (negsucc (S n)) = negsucc n

pred : ℤ → ℤ
pred (pos O) = negsucc O
pred (pos (S n)) = pos n
pred (negsucc n) = negsucc (S n)

abstract
  succ-pred : (n : ℤ) → succ (pred n) == n
  succ-pred (pos O) = idp
  succ-pred (pos (S n)) = idp
  succ-pred (negsucc n) = idp

  pred-succ : (n : ℤ) → pred (succ n) == n
  pred-succ (pos n) = idp
  pred-succ (negsucc O) = idp
  pred-succ (negsucc (S n)) = idp

succ-equiv : ℤ ≃ ℤ
succ-equiv = equiv succ pred succ-pred pred-succ

pred-injective : (z₁ z₂ : ℤ) → pred z₁ == pred z₂ → z₁ == z₂
pred-injective z₁ z₂ p = ! (succ-pred z₁) ∙ ap succ p ∙ succ-pred z₂

succ-injective : (z₁ z₂ : ℤ) → succ z₁ == succ z₂ → z₁ == z₂
succ-injective z₁ z₂ p = ! (pred-succ z₁) ∙ ap pred p ∙ pred-succ z₂

{- Converting between ℤ, ℕ, and ℕ₋₂ -}

ℤ-to-ℕ₋₂ : ℤ → ℕ₋₂
ℤ-to-ℕ₋₂ (pos m) = ⟨ m ⟩
ℤ-to-ℕ₋₂ (negsucc O) = -1
ℤ-to-ℕ₋₂ (negsucc _) = -2

ℕ-to-ℤ : ℕ → ℤ
ℕ-to-ℤ n = pos n


{- Proof that [ℤ] has decidable equality and hence is a set -}

private
  ℤ-get-pos : ℤ → ℕ
  ℤ-get-pos (pos n) = n
  ℤ-get-pos (negsucc n) = O

  ℤ-get-negsucc : ℤ → ℕ
  ℤ-get-negsucc (pos n) = O
  ℤ-get-negsucc (negsucc n) = n

  ℤ-negsucc≠pos-type : ℤ → Type₀
  ℤ-negsucc≠pos-type (pos n) = Empty
  ℤ-negsucc≠pos-type (negsucc n) = Unit

abstract
  pos-injective : (n m : ℕ) (p : pos n == pos m) → n == m
  pos-injective n m p = ap ℤ-get-pos p

  negsucc-injective : (n m : ℕ) (p : negsucc n == negsucc m) → n == m
  negsucc-injective n m p = ap ℤ-get-negsucc p

  ℤ-negsucc≠pos : (n m : ℕ) → negsucc n ≠ pos m
  ℤ-negsucc≠pos n m p = transport ℤ-negsucc≠pos-type p unit

  ℤ-pos≠negsucc : (n m : ℕ) → pos n ≠ negsucc m
  ℤ-pos≠negsucc n m p = transport ℤ-negsucc≠pos-type (! p) unit

  ℤ-has-dec-eq : has-dec-eq ℤ
  ℤ-has-dec-eq (pos n) (pos m) with ℕ-has-dec-eq n m
  ℤ-has-dec-eq (pos n) (pos m) | inl p = inl (ap pos p)
  ℤ-has-dec-eq (pos n) (pos m) | inr p⊥ = inr (λ p → p⊥ (pos-injective n m p))
  ℤ-has-dec-eq (pos n) (negsucc m) = inr (ℤ-pos≠negsucc n m)
  ℤ-has-dec-eq (negsucc n) (pos m) = inr (ℤ-negsucc≠pos n m)
  ℤ-has-dec-eq (negsucc n) (negsucc m) with ℕ-has-dec-eq n m
  ℤ-has-dec-eq (negsucc n) (negsucc m) | inl p = inl (ap negsucc p)
  ℤ-has-dec-eq (negsucc n) (negsucc m) | inr p⊥ = inr (λ p → p⊥ (negsucc-injective n m p))

  ℤ-is-set : is-set ℤ
  ℤ-is-set = dec-eq-is-set ℤ-has-dec-eq

ℤ-level = ℤ-is-set

{-
  ℤ is also a group!
-}

-- inv
ℤ~ : ℤ → ℤ
ℤ~ (pos (S n)) = negsucc n
ℤ~ (pos O) = pos O
ℤ~ (negsucc n) = pos (S n)

-- comp
infixl 80 _ℤ+_
_ℤ+_ : ℤ → ℤ → ℤ
pos O         ℤ+ z = z
pos (S n)     ℤ+ z = succ (pos n ℤ+ z)
negsucc O     ℤ+ z = pred z
negsucc (S n) ℤ+ z = pred (negsucc n ℤ+ z)

-- unit-l
ℤ+-unit-l : ∀ z → pos O ℤ+ z == z
ℤ+-unit-l _ = idp

-- unit-r
private
  ℤ+-unit-r-pos : ∀ n → pos n ℤ+ pos O == pos n
  ℤ+-unit-r-pos O     = idp
  ℤ+-unit-r-pos (S n) = ap succ $ ℤ+-unit-r-pos n

  ℤ+-unit-r-negsucc : ∀ n → negsucc n ℤ+ pos O == negsucc n
  ℤ+-unit-r-negsucc O     = idp
  ℤ+-unit-r-negsucc (S n) = ap pred $ ℤ+-unit-r-negsucc n

ℤ+-unit-r : ∀ z → z ℤ+ pos O == z
ℤ+-unit-r (pos n) = ℤ+-unit-r-pos n
ℤ+-unit-r (negsucc n) = ℤ+-unit-r-negsucc n

{-
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
-}
