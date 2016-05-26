{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.Relation
open import lib.NType
open import lib.types.Empty

module lib.types.Nat where

infixl 80 _+_
_+_ : ℕ → ℕ → ℕ
0 + n = n
(S m) + n = S (m + n)

{-# BUILTIN NATPLUS _+_ #-}

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

infix 120 _*2
_*2 : ℕ → ℕ
O *2 = O
(S n) *2 = S (S (n *2))

ℕ-pred : ℕ → ℕ
ℕ-pred 0 = 0
ℕ-pred (S n) = n

ℕ-S-inj : (n m : ℕ) (p : S n == S m) → n == m
ℕ-S-inj n m p = ap ℕ-pred p

private
  ℕ-S≠O-type : ℕ → Type₀
  ℕ-S≠O-type O = Empty
  ℕ-S≠O-type (S n) = Unit

abstract
  ℕ-S≠O : (n : ℕ) → S n ≠ O
  ℕ-S≠O n p = transport ℕ-S≠O-type p unit

  ℕ-O≠S : (n : ℕ) → (O ≠ S n)
  ℕ-O≠S n p = ℕ-S≠O n (! p)

  ℕ-has-dec-eq : has-dec-eq ℕ
  ℕ-has-dec-eq O O = inl idp
  ℕ-has-dec-eq O (S n) = inr (ℕ-O≠S n)
  ℕ-has-dec-eq (S n) O = inr (ℕ-S≠O n)
  ℕ-has-dec-eq (S n) (S m) with ℕ-has-dec-eq n m
  ℕ-has-dec-eq (S n) (S m) | inl p = inl (ap S p)
  ℕ-has-dec-eq (S n) (S m) | inr p⊥ = inr (λ p → p⊥ (ℕ-S-inj n m p))

  ℕ-is-set : is-set ℕ
  ℕ-is-set = dec-eq-is-set ℕ-has-dec-eq

ℕ-level = ℕ-is-set

{- Inequalities -}
infix 40 _<_ _<'_ _≤_ _≤'_
infix 40 _>_ _>'_

data _<_ : ℕ → ℕ → Type₀ where
  ltS : {m : ℕ} → m < (S m)
  ltSR : {m n : ℕ} → m < n → m < (S n)

data _<'_ : ℕ → ℕ → Type₀ where
  lt'O : {m : ℕ} → O <' S m
  lt'S : {m n : ℕ} → m <' n → (S m) <' (S n)

_≤_ : ℕ → ℕ → Type₀
m ≤ n = Coprod (m == n) (m < n)

_≤'_ : ℕ → ℕ → Type₀
m ≤' n = Coprod (m == n) (m <' n)

_>_ : ℕ → ℕ → Type₀
m > n = n < m

_>'_ : ℕ → ℕ → Type₀
m >' n = n <' m

-- [<] and [<'] are the same

<'-ltS : {m : ℕ} → m <' (S m)
<'-ltS {m = O} = lt'O
<'-ltS {m = S m} = lt'S <'-ltS

<'-ltSR : {m n : ℕ} → m <' n → m <' (S n)
<'-ltSR lt'O = lt'O
<'-ltSR (lt'S lt') = lt'S (<'-ltSR lt')

<-lt'O : {m : ℕ} → O < S m
<-lt'O {m = O} = ltS
<-lt'O {m = S m} = ltSR <-lt'O

<-lt'S : {m n : ℕ} → m < n → (S m) < (S n)
<-lt'S ltS = ltS
<-lt'S (ltSR lt) = ltSR (<-lt'S lt)

<-to-<' : {m n : ℕ} → m < n → m <' n
<-to-<' ltS = <'-ltS
<-to-<' (ltSR lt) = <'-ltSR (<-to-<' lt)

<'-to-< : {m n : ℕ} → m <' n → m < n
<'-to-< lt'O = <-lt'O
<'-to-< (lt'S lt') = <-lt'S (<'-to-< lt')

≤-to-≤' : {m n : ℕ} → m ≤ n → m ≤' n
≤-to-≤' (inl p) = inl p
≤-to-≤' (inr lt) = inr (<-to-<' lt)

≤'-to-≤ : {m n : ℕ} → m ≤' n → m ≤ n
≤'-to-≤ (inl p) = inl p
≤'-to-≤ (inr lt') = inr (<'-to-< lt')

-- properties of [<]

O<S : (m : ℕ) → O < S m
O<S m = <-lt'O

S>O = O<S

O≤ : (m : ℕ) → O ≤ m
O≤ O = inl idp
O≤ (S m) = inr (O<S m)

≮O : ∀ n → ¬ (n < O)
≮O _ ()

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
<-ap-S = <-lt'S

≤-ap-S : {m n : ℕ} → m ≤ n → S m ≤ S n
≤-ap-S (inl p) = inl (ap S p)
≤-ap-S (inr lt) = inr (<-ap-S lt)

≤'-ap-S : {m n : ℕ} → m ≤' n → S m ≤' S n
≤'-ap-S (inl p) = inl (ap S p)
≤'-ap-S (inr lt') = inr (lt'S lt')

<-cancel-S : {m n : ℕ} → S m < S n → m < n
<-cancel-S ltS = ltS
<-cancel-S (ltSR lt) = <-trans ltS lt

<'-cancel-S : {m n : ℕ} → S m <' S n → m <' n
<'-cancel-S (lt'S lt') = lt'

≤-cancel-S : {m n : ℕ} → S m ≤ S n → m ≤ n
≤-cancel-S (inl p) = inl (ap ℕ-pred p)
≤-cancel-S (inr lt) = inr (<-cancel-S lt)

≤'-cancel-S : {m n : ℕ} → S m ≤' S n → m ≤' n
≤'-cancel-S (inl p) = inl (ap ℕ-pred p)
≤'-cancel-S (inr lt) = inr (<'-cancel-S lt)

<-dec : Dec _<_
<-dec _     O     = inr (≮O _)
<-dec O     (S m) = inl (O<S m)
<-dec (S n) (S m) with <-dec n m
<-dec (S n) (S m) | inl p  = inl (<-ap-S p)
<-dec (S n) (S m) | inr p⊥ = inr (p⊥ ∘ <-cancel-S)

≯-to-≤ : {m n : ℕ} → ¬ (m > n) → m ≤ n
≯-to-≤ {O} {O} _ = inl idp
≯-to-≤ {O} {S n} _ = inr (O<S n)
≯-to-≤ {S m} {O} neggt = ⊥-elim $ neggt (S>O m)
≯-to-≤ {S m} {S n} neggt = ≤-ap-S (≯-to-≤ (neggt ∘ <-ap-S))

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
