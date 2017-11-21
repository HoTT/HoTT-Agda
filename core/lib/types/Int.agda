{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Nat
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

abstract
  pred-is-inj : is-inj pred
  pred-is-inj z₁ z₂ p = ! (succ-pred z₁) ∙ ap succ p ∙ succ-pred z₂

  pred-≠ : preserves-≠ pred
  pred-≠ = inj-preserves-≠ pred-is-inj

  succ-is-inj : is-inj succ
  succ-is-inj z₁ z₂ p = ! (pred-succ z₁) ∙ ap pred p ∙ pred-succ z₂

  succ-≠ : preserves-≠ succ
  succ-≠ = inj-preserves-≠ succ-is-inj

{- Converting between ℤ, ℕ, and ℕ₋₂ -}

ℤ-to-ℕ₋₂ : ℤ → ℕ₋₂
ℤ-to-ℕ₋₂ (pos m) = ⟨ m ⟩
ℤ-to-ℕ₋₂ (negsucc O) = -1
ℤ-to-ℕ₋₂ (negsucc _) = -2

ℕ-to-ℤ : ℕ → ℤ
ℕ-to-ℤ n = pos n

{- Proof that [ℤ] has decidable equality and hence is a set -}

abstract
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

  pos-is-inj : is-inj pos
  pos-is-inj n m p = ap ℤ-get-pos p

  ℕ-to-ℤ-is-inj : is-inj ℕ-to-ℤ
  ℕ-to-ℤ-is-inj = pos-is-inj

  pos-≠ : preserves-≠ pos
  pos-≠ = inj-preserves-≠ pos-is-inj

  ℕ-to-ℤ-≠ : preserves-≠ ℕ-to-ℤ
  ℕ-to-ℤ-≠ = pos-≠

  negsucc-is-inj : is-inj negsucc
  negsucc-is-inj n m p = ap ℤ-get-negsucc p

  negsucc-≠ : preserves-≠ negsucc
  negsucc-≠ = inj-preserves-≠ negsucc-is-inj

  ℤ-negsucc≠pos : (n m : ℕ) → negsucc n ≠ pos m
  ℤ-negsucc≠pos n m p = transport ℤ-negsucc≠pos-type p unit

  ℤ-pos≠negsucc : (n m : ℕ) → pos n ≠ negsucc m
  ℤ-pos≠negsucc n m p = transport ℤ-negsucc≠pos-type (! p) unit

  ℤ-has-dec-eq : has-dec-eq ℤ
  ℤ-has-dec-eq (pos n) (pos m) with ℕ-has-dec-eq n m
  ℤ-has-dec-eq (pos n) (pos m) | inl p = inl (ap pos p)
  ℤ-has-dec-eq (pos n) (pos m) | inr ¬p = inr (pos-≠ ¬p)
  ℤ-has-dec-eq (pos n) (negsucc m) = inr (ℤ-pos≠negsucc n m)
  ℤ-has-dec-eq (negsucc n) (pos m) = inr (ℤ-negsucc≠pos n m)
  ℤ-has-dec-eq (negsucc n) (negsucc m) with ℕ-has-dec-eq n m
  ℤ-has-dec-eq (negsucc n) (negsucc m) | inl p = inl (ap negsucc p)
  ℤ-has-dec-eq (negsucc n) (negsucc m) | inr ¬p = inr (negsucc-≠ ¬p)

  ℤ-is-set : is-set ℤ
  ℤ-is-set = dec-eq-is-set ℤ-has-dec-eq

  instance
    ℤ-level : {n : ℕ₋₂} → has-level (S (S n)) ℤ
    ℤ-level {⟨-2⟩} = ℤ-is-set
    ℤ-level {n = S n} = raise-level (S (S n)) ℤ-level

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

abstract
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

  -- assoc
  succ-+ : ∀ z₁ z₂ → succ z₁ ℤ+ z₂ == succ (z₁ ℤ+ z₂)
  succ-+ (pos n) _ = idp
  succ-+ (negsucc O) _ = ! $ succ-pred _
  succ-+ (negsucc (S _)) _ = ! $ succ-pred _

  pred-+ : ∀ z₁ z₂ → pred z₁ ℤ+ z₂ == pred (z₁ ℤ+ z₂)
  pred-+ (negsucc _) _ = idp
  pred-+ (pos O) _ = idp
  pred-+ (pos (S n)) _ = ! $ pred-succ _

  ℤ+-assoc : ∀ z₁ z₂ z₃ → (z₁ ℤ+ z₂) ℤ+ z₃ == z₁ ℤ+ (z₂ ℤ+ z₃)
  ℤ+-assoc (pos O)      z₂ z₃ = idp
  ℤ+-assoc (pos (S n₁)) z₂ z₃ =
    succ (pos n₁ ℤ+ z₂) ℤ+ z₃     =⟨ succ-+ (pos n₁ ℤ+ z₂) z₃ ⟩
    succ ((pos n₁ ℤ+ z₂) ℤ+ z₃)   =⟨ ap succ $ ℤ+-assoc (pos n₁) z₂ z₃ ⟩
    succ (pos n₁ ℤ+ (z₂ ℤ+ z₃))   =∎
  ℤ+-assoc (negsucc O)      z₂ z₃ = pred-+ z₂ z₃
  ℤ+-assoc (negsucc (S n₁)) z₂ z₃ =
    pred (negsucc n₁ ℤ+ z₂) ℤ+ z₃     =⟨ pred-+ (negsucc n₁ ℤ+ z₂) z₃ ⟩
    pred ((negsucc n₁ ℤ+ z₂) ℤ+ z₃)   =⟨ ap pred $ ℤ+-assoc (negsucc n₁) z₂ z₃ ⟩
    pred (negsucc n₁ ℤ+ (z₂ ℤ+ z₃))   =∎

  --comm
  ℤ+-succ : ∀ z₁ z₂ → z₁ ℤ+ succ z₂ == succ (z₁ ℤ+ z₂)
  ℤ+-succ (pos O) z₂ = idp
  ℤ+-succ (pos (S n)) z₂ = ap succ (ℤ+-succ (pos n) z₂)
  ℤ+-succ (negsucc O) z₂ = pred-succ z₂ ∙ ! (succ-pred z₂)
  ℤ+-succ (negsucc (S n)) z₂ =
    pred (negsucc n ℤ+ succ z₂)
      =⟨ ap pred (ℤ+-succ (negsucc n) z₂) ⟩
    pred (succ (negsucc n ℤ+ z₂))
      =⟨ pred-succ (negsucc n ℤ+ z₂) ⟩
    negsucc n ℤ+ z₂
      =⟨ ! $ succ-pred (negsucc n ℤ+ z₂) ⟩
    succ (pred (negsucc n ℤ+ z₂))
      =∎

  ℤ+-pred : ∀ z₁ z₂ → z₁ ℤ+ pred z₂ == pred (z₁ ℤ+ z₂)
  ℤ+-pred (pos O) z₂ = idp
  ℤ+-pred (pos (S n)) z₂ =
    succ (pos n ℤ+ pred z₂)
      =⟨ ap succ (ℤ+-pred (pos n) z₂) ⟩
    succ (pred (pos n ℤ+ z₂))
      =⟨ succ-pred (pos n ℤ+ z₂) ⟩
    pos n ℤ+ z₂
      =⟨ ! $ pred-succ (pos n ℤ+ z₂) ⟩
    pred (succ (pos n ℤ+ z₂))
      =∎
  ℤ+-pred (negsucc O) z₂ = idp
  ℤ+-pred (negsucc (S n)) z₂ = ap pred (ℤ+-pred (negsucc n) z₂)

  ℤ+-comm : ∀ z₁ z₂ → z₁ ℤ+ z₂ == z₂ ℤ+ z₁
  ℤ+-comm (pos O) z₂ = ! $ ℤ+-unit-r z₂
  ℤ+-comm (pos (S n₁)) z₂ =
    succ (pos n₁ ℤ+ z₂)
      =⟨ ℤ+-comm (pos n₁) z₂ |in-ctx succ ⟩
    succ (z₂ ℤ+ pos n₁)
      =⟨ ! $ ℤ+-succ z₂ (pos n₁) ⟩
    z₂ ℤ+ pos (S n₁)
      =∎
  ℤ+-comm (negsucc O) z₂ =
    pred z₂
      =⟨ ! $ ℤ+-unit-r z₂ |in-ctx pred ⟩
    pred (z₂ ℤ+ pos O)
      =⟨ ! $ ℤ+-pred z₂ (pos O) ⟩
    z₂ ℤ+ negsucc O
      =∎
  ℤ+-comm (negsucc (S n)) z₂ =
    pred (negsucc n ℤ+ z₂)
      =⟨ ℤ+-comm (negsucc n) z₂ |in-ctx pred ⟩
    pred (z₂ ℤ+ negsucc n)
      =⟨ ! $ ℤ+-pred z₂ (negsucc n) ⟩
    z₂ ℤ+ negsucc (S n)
      =∎

  private
    pos-S-ℤ+-negsucc-S : ∀ n₁ n₂ → pos (S n₁) ℤ+ negsucc (S n₂) == pos n₁ ℤ+ negsucc n₂
    pos-S-ℤ+-negsucc-S O      n₂ = idp
    pos-S-ℤ+-negsucc-S (S n₁) n₂ = ap succ $ pos-S-ℤ+-negsucc-S n₁ n₂

    negsucc-S-ℤ+-pos-S : ∀ n₁ n₂ → negsucc (S n₁) ℤ+ pos (S n₂) == negsucc n₁ ℤ+ pos n₂
    negsucc-S-ℤ+-pos-S O      n₂ = idp
    negsucc-S-ℤ+-pos-S (S n₁) n₂ = ap pred $ negsucc-S-ℤ+-pos-S n₁ n₂

  ℤ~-inv-r : ∀ z → z ℤ+ ℤ~ z == 0
  ℤ~-inv-r (pos O)     = idp
  ℤ~-inv-r (pos (S O)) = idp
  ℤ~-inv-r (pos (S (S n))) =
    pos (S (S n)) ℤ+ negsucc (S n)  =⟨ pos-S-ℤ+-negsucc-S (S n) n ⟩
    pos (S n) ℤ+ negsucc n          =⟨ ℤ~-inv-r (pos (S n)) ⟩
    0                               =∎
  ℤ~-inv-r (negsucc O) = idp
  ℤ~-inv-r (negsucc (S n)) =
    negsucc (S n) ℤ+ pos (S (S n))  =⟨ negsucc-S-ℤ+-pos-S n (S n) ⟩
    negsucc n ℤ+ pos (S n)          =⟨ ℤ~-inv-r (negsucc n) ⟩
    0                               =∎

  ℤ~-inv-l : ∀ z → ℤ~ z ℤ+ z == 0
  ℤ~-inv-l (pos O) = idp
  ℤ~-inv-l (pos (S n)) = ℤ~-inv-r (negsucc n)
  ℤ~-inv-l (negsucc n) = ℤ~-inv-r (pos (S n))

  -- More properties about [ℤ~]

  ℤ~-succ : ∀ z → ℤ~ (succ z) == pred (ℤ~ z)
  ℤ~-succ (pos 0) = idp
  ℤ~-succ (pos (S n)) = idp
  ℤ~-succ (negsucc 0) = idp
  ℤ~-succ (negsucc (S n)) = idp

  ℤ~-pred : ∀ z → ℤ~ (pred z) == succ (ℤ~ z)
  ℤ~-pred (pos 0) = idp
  ℤ~-pred (pos 1) = idp
  ℤ~-pred (pos (S (S n))) = idp
  ℤ~-pred (negsucc 0) = idp
  ℤ~-pred (negsucc (S n)) = idp

  ℤ~-+ : ∀ z₁ z₂ → ℤ~ (z₁ ℤ+ z₂) == ℤ~ z₁ ℤ+ ℤ~ z₂
  ℤ~-+ (pos 0)         z₂ = idp
  ℤ~-+ (pos 1)         z₂ = ℤ~-succ z₂
  ℤ~-+ (pos (S (S n))) z₂ =
    ℤ~-succ (pos (S n) ℤ+ z₂) ∙ ap pred (ℤ~-+ (pos (S n)) z₂)
  ℤ~-+ (negsucc O)     z₂ = ℤ~-pred z₂
  ℤ~-+ (negsucc (S n)) z₂ =
    ℤ~-pred (negsucc n ℤ+ z₂) ∙ ap succ (ℤ~-+ (negsucc n) z₂)

  ℤ+-cancel-l : ∀ z₁ {z₂ z₃} → z₁ ℤ+ z₂ == z₁ ℤ+ z₃ → z₂ == z₃
  ℤ+-cancel-l z₁ {z₂} {z₃} p =
      ap (_ℤ+ z₂) (! $ ℤ~-inv-l z₁)
    ∙ ℤ+-assoc (ℤ~ z₁) z₁ z₂
    ∙ ap (ℤ~ z₁ ℤ+_) p
    ∙ ! (ℤ+-assoc (ℤ~ z₁) z₁ z₃)
    ∙ ap (_ℤ+ z₃) (ℤ~-inv-l z₁)
