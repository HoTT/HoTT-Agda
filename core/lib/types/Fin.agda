{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Nat
open import lib.types.Subtype

module lib.types.Fin where

Fin : ℕ → Type₀
Fin n = Σ ℕ (_< n)

instance
  Fin-reader : ∀ {n} → FromNat (Fin n)
  FromNat.in-range (Fin-reader {n}) m = m < n
  FromNat.read (Fin-reader {n}) m ⦃ m<n ⦄ = m , m<n

Fin-S : ∀ {n} → Fin n → Fin (S n)
Fin-S (n , lt) = n , ltSR lt

Fin-S^ : ∀ {n} → (m : ℕ) → Fin n → Fin (m + n)
Fin-S^ O <n = <n
Fin-S^ (S m) <n = Fin-S (Fin-S^ m <n)

Fin-S^' : ∀ {n} → (m : ℕ) → Fin n → Fin (ℕ-S^' m n)
Fin-S^' O <n = <n
Fin-S^' (S m) <n = Fin-S^' m (Fin-S <n)

Fin-to-≠ : ∀ {n} (<n : Fin n) → fst <n ≠ n
Fin-to-≠ <n = <-to-≠ (snd <n)

Fin-prop : ℕ → SubtypeProp ℕ lzero
Fin-prop n = ((_< n) , λ _ → <-is-prop)

abstract
  Fin-is-set : {n : ℕ} → is-set (Fin n)
  Fin-is-set {n} = Subtype-level (Fin-prop n)

  Fin-has-dec-eq : {n : ℕ} → has-dec-eq (Fin n)
  Fin-has-dec-eq {n} = Subtype-has-dec-eq (Fin-prop n) ℕ-has-dec-eq

private
  Fin-pred=-type : {n : ℕ} → Fin n → Fin n → Type₀
  Fin-pred=-type (_ , ltSR _) (_ , ltS) = ⊤
  Fin-pred=-type (_ , ltS) (_ , ltSR _) = ⊤
  Fin-pred=-type (m , ltS) (n , ltS) = m == n :> ℕ
  Fin-pred=-type {S n} (m , ltSR m<n) (o , ltSR o<n) = (m , m<n) == (o , o<n) :> Fin n

  Fin-pred= : {n : ℕ} {x y : Fin n} → x == y → Fin-pred=-type x y
  Fin-pred= {x = (_ , ltS)} idp = idp
  Fin-pred= {x = (_ , ltSR _)} idp = idp

abstract
  ltSR≠ltS : ∀ {m} (<m : Fin m) → Fin-S <m ≠ (m , ltS)
  ltSR≠ltS <m = Fin-to-≠ <m ∘ ap fst

  ltS≠ltSR : ∀ {m} (<m : Fin m) → (m , ltS) ≠ Fin-S <m
  ltS≠ltSR <m = Fin-to-≠ <m ∘ ! ∘ ap fst

abstract
  Fin-S-is-inj : ∀ {n} → is-inj (Fin-S {n = n})
  Fin-S-is-inj _ _ = Fin-pred=

  Fin-S-≠ : ∀ {n} {<n₀ <n₁ : Fin n} (p : <n₀ ≠ <n₁) → Fin-S <n₀ ≠ Fin-S <n₁
  Fin-S-≠ {<n₀ = <n₀} {<n₁} p = p ∘ Fin-S-is-inj <n₀ <n₁

  Fin-S^-≠ : ∀ {n} m {<n₀ <n₁ : Fin n} (p : <n₀ ≠ <n₁) → Fin-S^ m <n₀ ≠ Fin-S^ m <n₁
  Fin-S^-≠ O p = p
  Fin-S^-≠ (S n) p = Fin-S-≠ (Fin-S^-≠ n p)

  Fin-S^'-≠ : ∀ {n} m {<n₀ <n₁ : Fin n} (p : <n₀ ≠ <n₁) → Fin-S^' m <n₀ ≠ Fin-S^' m <n₁
  Fin-S^'-≠ O p = p
  Fin-S^'-≠ (S n) p = Fin-S^'-≠ n (Fin-S-≠ p)

Fin-equiv-Empty : Fin 0 ≃ Empty
Fin-equiv-Empty = equiv to from to-from from-to where
  to : Fin 0 → Empty
  to (_ , ())

  from : Empty → Fin 0
  from ()

  abstract
    to-from : ∀ x → to (from x) == x
    to-from ()

    from-to : ∀ x → from (to x) == x
    from-to (_ , ())

Fin-equiv-Coprod : {n : ℕ} → Fin (S n) ≃ Fin n ⊔ Unit
Fin-equiv-Coprod {n} = equiv to from to-from from-to where
  to : Fin (S n) → Fin n ⊔ Unit
  to (m , ltS) = inr unit
  to (m , ltSR lt) = inl (m , lt)

  from : Fin n ⊔ Unit → Fin (S n)
  from (inr _) = n , ltS
  from (inl fin) = Fin-S fin

  abstract
    to-from : ∀ x → to (from x) == x
    to-from (inr _) = idp
    to-from (inl _) = idp

    from-to : ∀ x → from (to x) == x
    from-to (_ , ltS) = idp
    from-to (_ , ltSR _) = idp
