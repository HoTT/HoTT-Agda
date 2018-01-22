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

Fin-prop : ℕ → SubtypeProp ℕ lzero
Fin-prop n = ((_< n) , λ _ → <-is-prop)

Fin-is-set : {n : ℕ} → is-set (Fin n)
Fin-is-set {n} = Subtype-level (Fin-prop n)

Fin-has-dec-eq : {n : ℕ} → has-dec-eq (Fin n)
Fin-has-dec-eq {n} = Subtype-has-dec-eq (Fin-prop n) ℕ-has-dec-eq

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
