{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.types.Nat

module lib.types.TLevel where

_-2 : ℕ → ℕ₋₂
O -2 = ⟨-2⟩
(S n) -2 = S (n -2)

_-1 : ℕ → ℕ₋₂
O -1 = ⟨-1⟩
(S n) -1 = S (n -1)

⟨_⟩ : ℕ → ℕ₋₂
⟨ n ⟩ = S (S (n -2))

⟨1⟩ = ⟨ 1 ⟩
⟨2⟩ = ⟨ 2 ⟩

_+2+_ : ℕ₋₂ → ℕ₋₂ → ℕ₋₂
⟨-2⟩ +2+ n = n
S m +2+ n = S (m +2+ n)

+2+-unit-r : (m : ℕ₋₂) → m +2+ ⟨-2⟩ == m
+2+-unit-r ⟨-2⟩ = idp
+2+-unit-r (S m) = ap S (+2+-unit-r m)

+2+-βr : (m n : ℕ₋₂) → m +2+ (S n) == S (m +2+ n)
+2+-βr ⟨-2⟩ n = idp
+2+-βr (S m) n = ap S (+2+-βr m n)

+2+-comm : (m n : ℕ₋₂) → m +2+ n == n +2+ m
+2+-comm m ⟨-2⟩ = +2+-unit-r m
+2+-comm m (S n) = +2+-βr m n ∙ ap S (+2+-comm m n)

{- Inequalities -}
data _<T_ : ℕ₋₂ → ℕ₋₂ → Type₀ where
  ltS : {m : ℕ₋₂} → m <T (S m)
  ltSR : {m n : ℕ₋₂} → m <T n → m <T (S n)

_≤T_ : ℕ₋₂ → ℕ₋₂ → Type₀
m ≤T n = Coprod (m == n) (m <T n) 

-2<T : (m : ℕ₋₂) → ⟨-2⟩ <T S m
-2<T ⟨-2⟩ = ltS
-2<T (S m) = ltSR (-2<T m)

-2≤T : (m : ℕ₋₂) → ⟨-2⟩ ≤T m
-2≤T ⟨-2⟩ = inl idp
-2≤T (S m) = inr (-2<T m)

<T-trans : {m n k : ℕ₋₂} → m <T n → n <T k → m <T k
<T-trans lt₁ ltS = ltSR lt₁
<T-trans lt₁ (ltSR lt₂) = ltSR (<T-trans lt₁ lt₂)

≤T-trans : {m n k : ℕ₋₂} → m ≤T n → n ≤T k → m ≤T k
≤T-trans {k = k} (inl p₁) lte₂ = transport (λ t → t ≤T k) (! p₁) lte₂
≤T-trans {m = m} lte₁ (inl p₂) = transport (λ t → m ≤T t) p₂ lte₁
≤T-trans (inr lt₁) (inr lt₂) = inr (<T-trans lt₁ lt₂)

<T-ap-S : {m n : ℕ₋₂} → m <T n → S m <T S n
<T-ap-S ltS = ltS
<T-ap-S (ltSR lt) = ltSR (<T-ap-S lt)

≤T-ap-S : {m n : ℕ₋₂} → m ≤T n → S m ≤T S n
≤T-ap-S (inl p) = inl (ap S p)
≤T-ap-S (inr lt) = inr (<T-ap-S lt)

<T-cancel-S : {m n : ℕ₋₂} → S m <T S n → m <T n
<T-cancel-S ltS = ltS
<T-cancel-S (ltSR lt) = <T-trans ltS lt

<T-+2+-l : {m n : ℕ₋₂} (k : ℕ₋₂) → m <T n → (k +2+ m) <T (k +2+ n)
<T-+2+-l ⟨-2⟩ lt = lt
<T-+2+-l (S k) lt = <T-ap-S (<T-+2+-l k lt)

≤T-+2+-l : {m n : ℕ₋₂} (k : ℕ₋₂) → m ≤T n → (k +2+ m) ≤T (k +2+ n)
≤T-+2+-l k (inl p) = inl (ap (λ t → k +2+ t) p)
≤T-+2+-l k (inr lt) = inr (<T-+2+-l k lt)

<T-+2+-r : {m n : ℕ₋₂} (k : ℕ₋₂) → m <T n → (m +2+ k) <T (n +2+ k)
<T-+2+-r k ltS = ltS
<T-+2+-r k (ltSR lt) = ltSR (<T-+2+-r k lt)

≤T-+2+-r : {m n : ℕ₋₂} (k : ℕ₋₂) → m ≤T n → (m +2+ k) ≤T (n +2+ k)
≤T-+2+-r k (inl p) = inl (ap (λ t → t +2+ k) p)
≤T-+2+-r k (inr lt) = inr (<T-+2+-r k lt)

<T-witness : {m n : ℕ₋₂} → (m <T n) → Σ ℕ₋₂ (λ k → S k +2+ m == n)
<T-witness ltS = (⟨-2⟩ , idp)
<T-witness (ltSR lt) = let w' = <T-witness lt in (S (fst w') , ap S (snd w'))

≤T-witness : {m n : ℕ₋₂} → (m ≤T n) → Σ ℕ₋₂ (λ k → k +2+ m == n)
≤T-witness (inl p) = (⟨-2⟩ , p)
≤T-witness (inr lt) = let w' = <T-witness lt in (S (fst w') , snd w')

-2-monotone-< : {m n : ℕ} → (m < n) → (m -2 <T n -2)
-2-monotone-< ltS = ltS
-2-monotone-< (ltSR lt) = ltSR (-2-monotone-< lt)

-2-monotone-≤ : {m n : ℕ} → (m ≤ n) → (m -2 ≤T n -2)
-2-monotone-≤ (inl p) = inl (ap _-2 p)
-2-monotone-≤ (inr lt) = inr (-2-monotone-< lt)

⟨⟩-monotone-< : {m n : ℕ} → (m < n) → (⟨ m ⟩ <T ⟨ n ⟩)
⟨⟩-monotone-< ltS = ltS
⟨⟩-monotone-< (ltSR lt) = ltSR (⟨⟩-monotone-< lt)

⟨⟩-monotone-≤ : {m n : ℕ} → (m ≤ n) → (⟨ m ⟩ ≤T ⟨ n ⟩)
⟨⟩-monotone-≤ (inl p) = inl (ap ⟨_⟩ p)
⟨⟩-monotone-≤ (inr lt) = inr (⟨⟩-monotone-< lt)

minT : ℕ₋₂ → ℕ₋₂ → ℕ₋₂
minT ⟨-2⟩ n = ⟨-2⟩
minT (S m) ⟨-2⟩ = ⟨-2⟩
minT (S m) (S n) = S (minT m n)

minT≤l : (m n : ℕ₋₂) → minT m n ≤T m
minT≤l ⟨-2⟩ n = inl idp
minT≤l (S m) ⟨-2⟩ = -2≤T (S m)
minT≤l (S m) (S n) = ≤T-ap-S (minT≤l m n)

minT≤r : (m n : ℕ₋₂) → minT m n ≤T n
minT≤r ⟨-2⟩ n = -2≤T n
minT≤r (S m) ⟨-2⟩ = inl idp
minT≤r (S m) (S n) = ≤T-ap-S (minT≤r m n)

minT-out : (m n : ℕ₋₂) → Coprod (minT m n == m) (minT m n == n)
minT-out ⟨-2⟩ _ = inl idp
minT-out (S _) ⟨-2⟩ = inr idp
minT-out (S m) (S n) with minT-out m n
minT-out (S m) (S n) | inl p = inl (ap S p)
minT-out (S m) (S n) | inr q = inr (ap S q)

