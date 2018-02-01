{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.Function
open import lib.NType
open import lib.PathGroupoid
open import lib.Relation
open import lib.types.Coproduct
open import lib.types.Empty

module lib.types.Nat where

infixl 80 _+_
_+_ : ℕ → ℕ → ℕ
0 + n = n
(S m) + n = S (m + n)

{-# BUILTIN NATPLUS _+_ #-}

abstract
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

-- the [+] is like [ℕ-S^]
ℕ-S^' : ℕ → ℕ → ℕ
ℕ-S^' O n = n
ℕ-S^' (S m) n = ℕ-S^' m (S n)

ℕ-pred : ℕ → ℕ
ℕ-pred 0 = 0
ℕ-pred (S n) = n

abstract
  ℕ-S-is-inj : is-inj (S :> (ℕ → ℕ))
  ℕ-S-is-inj n m p = ap ℕ-pred p

  ℕ-S-≠ : ∀ {n m : ℕ} (p : n ≠ m) → S n ≠ S m :> ℕ
  ℕ-S-≠ {n} {m} p = p ∘ ℕ-S-is-inj n m

  private
    ℕ-S≠O-type : ℕ → Type₀
    ℕ-S≠O-type O = Empty
    ℕ-S≠O-type (S n) = Unit

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
  ℕ-has-dec-eq (S n) (S m) | inr ¬p = inr (ℕ-S-≠ ¬p)

ℕ-is-set : is-set ℕ
ℕ-is-set = dec-eq-is-set ℕ-has-dec-eq

instance
  ℕ-level : {n : ℕ₋₂} → has-level (S (S n)) ℕ
  ℕ-level {⟨-2⟩} = ℕ-is-set
  ℕ-level {n = S n} = raise-level (S (S n)) ℕ-level

{- Inequalities -}
infix 40 _<_ _≤_

data _<_ : ℕ → ℕ → Type₀ where
  ltS : {m : ℕ} → m < (S m)
  ltSR : {m n : ℕ} → m < n → m < (S n)

_≤_ : ℕ → ℕ → Type₀
m ≤ n = Coprod (m == n) (m < n)

-- experimental: [lteE] [lteS] [lteSR]
lteE : {m : ℕ} → m ≤ m
lteE = inl idp

lteS : {m : ℕ} → m ≤ S m
lteS = inr ltS

lteSR : {m n : ℕ} → m ≤ n → m ≤ (S n)
lteSR (inl idp) = lteS
lteSR (inr lt) = inr (ltSR lt)

-- properties of [<]

O<S : (m : ℕ) → O < S m
O<S O = ltS
O<S (S m) = ltSR (O<S m)

O≤ : (m : ℕ) → O ≤ m
O≤ O = inl idp
O≤ (S m) = inr (O<S m)

≮O : ∀ n → ¬ (n < O)
≮O _ ()

S≰O : ∀ n → ¬ (S n ≤ O)
S≰O _ (inl ())
S≰O _ (inr ())

<-trans : {m n k : ℕ} → m < n → n < k → m < k
<-trans lt₁ ltS = ltSR lt₁
<-trans lt₁ (ltSR lt₂) = ltSR (<-trans lt₁ lt₂)

≤-refl : {m : ℕ} → m ≤ m
≤-refl = lteE

≤-trans : {m n k : ℕ} → m ≤ n → n ≤ k → m ≤ k
≤-trans (inl idp) lte₂ = lte₂
≤-trans lte₁ (inl idp) = lte₁
≤-trans (inr lt₁) (inr lt₂) = inr (<-trans lt₁ lt₂)

private
  test₀ : {m n : ℕ} (m≤n : m ≤ n) → lteSR m≤n == ≤-trans m≤n lteS
  test₀ (inl idp) = idp
  test₀ (inr lt) = idp

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
≤-cancel-S (inl p) = inl (ap ℕ-pred p)
≤-cancel-S (inr lt) = inr (<-cancel-S lt)

<-dec : Decidable _<_
<-dec _ O = inr (≮O _)
<-dec O (S m) = inl (O<S m)
<-dec (S n) (S m) with <-dec n m
<-dec (S n) (S m) | inl p = inl (<-ap-S p)
<-dec (S n) (S m) | inr ¬p = inr (¬p ∘ <-cancel-S)

≤-dec : Decidable _≤_
≤-dec O m = inl (O≤ m)
≤-dec (S n) O = inr (S≰O n)
≤-dec (S n) (S m) with ≤-dec n m
≤-dec (S n) (S m) | inl p = inl (≤-ap-S p)
≤-dec (S n) (S m) | inr ¬p = inr (¬p ∘ ≤-cancel-S)

abstract
  <-to-≠ : {m n : ℕ} → m < n → m ≠ n
  <-to-≠ {m = O} ltS = ℕ-O≠S _
  <-to-≠ {m = O} (ltSR lt) = ℕ-O≠S _
  <-to-≠ {m = S m} {n = O} ()
  <-to-≠ {m = S m} {n = S n} lt = ℕ-S-≠ (<-to-≠ (<-cancel-S lt))

  <-to-≱ : {m n : ℕ} → m < n → ¬ (n ≤ m)
  <-to-≱ m<n (inl idp) = <-to-≠ m<n idp
  <-to-≱ m<n (inr n<m) = <-to-≠ (<-trans m<n n<m) idp

  <-has-all-paths : {m n : ℕ} → has-all-paths (m < n)
  <-has-all-paths = <-has-all-paths' idp where
    <-has-all-paths' : {m n₁ n₂ : ℕ} (eqn : n₁ == n₂) (lt₁ : m < n₁) (lt₂ : m < n₂)
      → PathOver (λ n → m < n) eqn lt₁ lt₂
    <-has-all-paths' eqn ltS ltS = transport (λ eqn₁ → PathOver (_<_ _) eqn₁ ltS ltS)
      (prop-has-all-paths idp eqn) idp
    <-has-all-paths' idp ltS (ltSR lt₂) = ⊥-rec (<-to-≠ lt₂ idp)
    <-has-all-paths' idp (ltSR lt₁) ltS = ⊥-rec (<-to-≠ lt₁ idp)
    <-has-all-paths' idp (ltSR lt₁) (ltSR lt₂) = ap ltSR (<-has-all-paths' idp lt₁ lt₂)

  instance
    <-is-prop : {m n : ℕ} → is-prop (m < n)
    <-is-prop = all-paths-is-prop <-has-all-paths

  ≤-has-all-paths : {m n : ℕ} → has-all-paths (m ≤ n)
  ≤-has-all-paths = λ{
    (inl eq₁) (inl eq₂) → ap inl (prop-has-all-paths eq₁ eq₂);
    (inl eq)  (inr lt)  → ⊥-rec (<-to-≠ lt eq);
    (inr lt)  (inl eq)  → ⊥-rec (<-to-≠ lt eq);
    (inr lt₁) (inr lt₂) → ap inr (<-has-all-paths lt₁ lt₂)}

  instance
    ≤-is-prop : {m n : ℕ} → is-prop (m ≤ n)
    ≤-is-prop = all-paths-is-prop ≤-has-all-paths

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

-- Double

infix 120 _*2
_*2 : ℕ → ℕ
O *2 = O
(S n) *2 = S (S (n *2))

*2-increasing : (m : ℕ) → (m ≤ m *2)
*2-increasing O = inl idp
*2-increasing (S m) = ≤-trans (≤-ap-S (*2-increasing m)) (inr ltS)

*2-monotone-< : {m n : ℕ} → m < n → m *2 < n *2
*2-monotone-< ltS = ltSR ltS
*2-monotone-< (ltSR lt) = ltSR (ltSR (*2-monotone-< lt))

*2-monotone-≤ : {m n : ℕ} → m ≤ n → m *2 ≤ n *2
*2-monotone-≤ (inl p) = inl (ap _*2 p)
*2-monotone-≤ (inr lt) = inr (*2-monotone-< lt)

-- Trichotomy

ℕ-trichotomy : (m n : ℕ) → (m == n) ⊔ ((m < n) ⊔ (n < m))
ℕ-trichotomy O O = inl idp
ℕ-trichotomy O (S n) = inr (inl (O<S n))
ℕ-trichotomy (S m) O = inr (inr (O<S m))
ℕ-trichotomy (S m) (S n) with ℕ-trichotomy m n
ℕ-trichotomy (S m) (S n) | inl m=n = inl (ap S m=n)
ℕ-trichotomy (S m) (S n) | inr (inl m<n) = inr (inl (<-ap-S m<n))
ℕ-trichotomy (S m) (S n) | inr (inr m>n) = inr (inr (<-ap-S m>n))
