{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.NType
open import lib.types.Empty

module lib.types.Nat where

data ℕ : Type₀ where
  O : ℕ
  S : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO O #-}
{-# BUILTIN SUC S #-}

Nat = ℕ

_+_ : ℕ → ℕ → ℕ
0 + n = n
(S m) + n = S (m + n)

+-unit-r : (m : ℕ) → m + 0 == m
+-unit-r 0     = idp
+-unit-r (S m) = ap S (+-unit-r m)

+-βr : (m n : ℕ) → m + (S n) == S (m + n)
+-βr 0     n = idp
+-βr (S m) n = ap S (+-βr m n)

+-comm : (m n : ℕ) → m + n == n + m
+-comm m 0     = +-unit-r m
+-comm m (S n) = +-βr m n ∙ ap S (+-comm m n)

+-assoc : (k m n : ℕ) → (k + m) + n == k + (m + n)
+-assoc 0     m n = idp
+-assoc (S k) m n = ap S (+-assoc k m n)

_*2 : ℕ → ℕ
O *2 = O
(S n) *2 = S (S (n *2))

private
  ℕ-get-S : ℕ → ℕ
  ℕ-get-S 0 = 42
  ℕ-get-S (S n) = n

  S-injective : (n m : ℕ) (p : S n == S m) → n == m
  S-injective n m p = ap ℕ-get-S p

  ℕ-S≠O-type : ℕ → Type₀
  ℕ-S≠O-type O = Empty
  ℕ-S≠O-type (S n) = Unit

abstract
  ℕ-S≠O : (n : ℕ) → S n ≠ O
  ℕ-S≠O n p = transport ℕ-S≠O-type p unit

  ℕ-S≠O#instance : {n : ℕ} → (S n ≠ O)
  ℕ-S≠O#instance {n} = ℕ-S≠O n

  ℕ-O≠S : (n : ℕ) → (O ≠ S n)
  ℕ-O≠S n p = ℕ-S≠O n (! p)

  ℕ-has-dec-eq : has-dec-eq ℕ
  ℕ-has-dec-eq O O = inl idp
  ℕ-has-dec-eq O (S n) = inr (ℕ-O≠S n)
  ℕ-has-dec-eq (S n) O = inr (ℕ-S≠O n)
  ℕ-has-dec-eq (S n) (S m) with ℕ-has-dec-eq n m
  ℕ-has-dec-eq (S n) (S m) | inl p = inl (ap S p)
  ℕ-has-dec-eq (S n) (S m) | inr p⊥ = inr (λ p → p⊥ (S-injective n m p))

  ℕ-is-set : is-set ℕ
  ℕ-is-set = dec-eq-is-set ℕ-has-dec-eq

ℕ-level = ℕ-is-set

{- Inequalities -}
infix 4 _<_
infix 4 _≤_

data _<_ : ℕ → ℕ → Type₀ where
  ltS : {m : ℕ} → m < (S m)
  ltSR : {m n : ℕ} → m < n → m < (S n)

_≤_ : ℕ → ℕ → Type₀
m ≤ n = Coprod (m == n) (m < n) 

O< : (m : ℕ) → O < S m
O< O = ltS
O< (S m) = ltSR (O< m)

O≤ : (m : ℕ) → O ≤ m
O≤ O = inl idp
O≤ (S m) = inr (O< m)

<-trans : {m n k : ℕ} → m < n → n < k → m < k
<-trans lt₁ ltS = ltSR lt₁
<-trans lt₁ (ltSR lt₂) = ltSR (<-trans lt₁ lt₂)

≤-refl : {m : ℕ} → m ≤ m
≤-refl = inl idp

≤-trans : {m n k : ℕ} → m ≤ n → n ≤ k → m ≤ k
≤-trans {k = k} (inl p₁) lte₂ = transport (λ t → t ≤ k) (! p₁) lte₂
≤-trans {m = m} lte₁ (inl p₂) = transport (λ t → m ≤ t) p₂ lte₁
≤-trans (inr lt₁) (inr lt₂) = inr (<-trans lt₁ lt₂)

<-ap-S : {m n : ℕ} → m < n → S m < S n
<-ap-S ltS = ltS
<-ap-S (ltSR lt) = ltSR (<-ap-S lt)

≤-ap-S : {m n : ℕ} → m ≤ n → S m ≤ S n
≤-ap-S (inl p) = inl (ap S p)
≤-ap-S (inr lt) = inr (<-ap-S lt)

<-cancel-S : {m n : ℕ} → S m < S n → m < n
<-cancel-S ltS = ltS
<-cancel-S (ltSR lt) = <-trans ltS lt

≤-cancel-S : {m n : ℕ} → S m ≤ S n → m ≤ n
≤-cancel-S (inl p) = inl (ap ℕ-get-S p)
≤-cancel-S (inr lt) = inr (<-cancel-S lt)

<-+-l : {m n : ℕ} (k : ℕ) → m < n → (k + m) < (k + n)
<-+-l O lt = lt
<-+-l (S k) lt = <-ap-S (<-+-l k lt)

≤-+-l : {m n : ℕ} (k : ℕ) → m ≤ n → (k + m) ≤ (k + n)
≤-+-l k (inl p) = inl (ap (λ t → k + t) p)
≤-+-l k (inr lt) = inr (<-+-l k lt)

<-+-r : {m n : ℕ} (k : ℕ) → m < n → (m + k) < (n + k)
<-+-r k ltS = ltS
<-+-r k (ltSR lt) = ltSR (<-+-r k lt)

≤-+-r : {m n : ℕ} (k : ℕ) → m ≤ n → (m + k) ≤ (n + k)
≤-+-r k (inl p) = inl (ap (λ t → t + k) p)
≤-+-r k (inr lt) = inr (<-+-r k lt)

<-witness : {m n : ℕ} → (m < n) → Σ ℕ (λ k → S k + m == n)
<-witness ltS = (O , idp)
<-witness (ltSR lt) = let w' = <-witness lt in (S (fst w') , ap S (snd w'))

≤-witness : {m n : ℕ} → (m ≤ n) → Σ ℕ (λ k → k + m == n)
≤-witness (inl p) = (O , p)
≤-witness (inr lt) = let w' = <-witness lt in (S (fst w') , snd w')

*2-increasing : (m : ℕ) → (m ≤ m *2)
*2-increasing O = inl idp
*2-increasing (S m) = ≤-trans (≤-ap-S (*2-increasing m)) (inr ltS)

*2-monotone-< : {m n : ℕ} → m < n → m *2 < n *2
*2-monotone-< ltS = ltSR ltS
*2-monotone-< (ltSR lt) = ltSR (ltSR (*2-monotone-< lt))

*2-monotone-≤ : {m n : ℕ} → m ≤ n → m *2 ≤ n *2
*2-monotone-≤ (inl p) = inl (ap _*2 p)
*2-monotone-≤ (inr lt) = inr (*2-monotone-< lt)
