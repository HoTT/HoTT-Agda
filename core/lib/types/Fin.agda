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

Fin-basis : ∀ {i} {I : ℕ} (X : Fin I → Ptd i)
  → (<I : Fin I) (x : de⊙ (X <I))
  → Π (Fin I) (de⊙ ∘ X)
Fin-basis X (_ , ltS) x (_ , ltS) = x
Fin-basis X (_ , ltSR lt₀) x (_ , ltSR lt₁) =
  Fin-basis (X ∘ Fin-S) (_ , lt₀) x (_ , lt₁)
Fin-basis X (_ , ltSR _) x (_ , ltS) = pt (X (_ , ltS))
Fin-basis X (_ , ltS) x (_ , ltSR lt) = pt (X (_ , ltSR lt))

Fin-basis-diag : ∀ {i} {I : ℕ} (X : Fin I → Ptd i) <I g
  → Fin-basis X <I g <I == g
Fin-basis-diag X (_ , ltS) g = idp
Fin-basis-diag X (_ , ltSR <I) g = Fin-basis-diag (X ∘ Fin-S) (_ , <I) g

Fin-basis-≠ : ∀ {i} {I : ℕ} (X : Fin I → Ptd i) <I g {<J}
  → <I ≠ <J → Fin-basis X <I g <J == pt (X <J)
Fin-basis-≠ X (_ , ltS) g {_ , ltS} neq = ⊥-elim (neq idp)
Fin-basis-≠ X (_ , ltSR lt₀) g {_ , ltSR lt₁} neq =
  Fin-basis-≠ (X ∘ Fin-S) (_ , lt₀) g {_ , lt₁} (neq ∘ ap Fin-S)
Fin-basis-≠ X (_ , ltSR _) g {_ , ltS} neq = idp
Fin-basis-≠ X (_ , ltS) g {_ , ltSR _} neq = idp

private
  Fin-basis-late' : ∀ {i} m n {I : ℕ} (X : Fin (ℕ-S^' m (n + S I)) → Ptd i) <I g
    →  Fin-basis X (Fin-S^' m (Fin-S^ n (Fin-S <I))) g (Fin-S^' m (Fin-S^ n (I , ltS)))
    == pt (X (Fin-S^' m (Fin-S^ n (I , ltS))))
  Fin-basis-late' O O X <I g = idp
  Fin-basis-late' O (S n) X <I g = Fin-basis-late' O n (X ∘ Fin-S) <I g
  Fin-basis-late' (S m) n X <I g = Fin-basis-late' m (S n) X <I g

Fin-basis-late : ∀ {i} m {I : ℕ} (X : Fin (ℕ-S^' (S m) I) → Ptd i) <I g
  →  Fin-basis X (Fin-S^' (S m) <I) g (Fin-S^' m (I , ltS))
  == pt (X (Fin-S^' m (I , ltS)))
Fin-basis-late m = Fin-basis-late' m O

private
  Fin-basis-early' : ∀ {i} m n {I : ℕ} (X : Fin (ℕ-S^' m (n + S I)) → Ptd i) <I g
    →  Fin-basis X (Fin-S^' m (Fin-S^ n (I , ltS))) g (Fin-S^' m (Fin-S^ n (Fin-S <I)))
    == pt (X (Fin-S^' m (Fin-S^ n (Fin-S <I))))
  Fin-basis-early' O O X <I g = idp
  Fin-basis-early' O (S n) X <I g = Fin-basis-early' O n (X ∘ Fin-S) <I g
  Fin-basis-early' (S m) n X <I g = Fin-basis-early' m (S n) X <I g

Fin-basis-early : ∀ {i} m {I : ℕ} (X : Fin (ℕ-S^' (S m) I) → Ptd i) <I g
  →  Fin-basis X (Fin-S^' m (I , ltS)) g (Fin-S^' (S m) <I)
  == pt (X (Fin-S^' (S m) <I))
Fin-basis-early m = Fin-basis-early' m O

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
  Fin-S-inj : ∀ {n} → is-inj (Fin-S {n = n})
  Fin-S-inj _ _ = Fin-pred=

  Fin-S^-inj : ∀ {n} m → is-inj (Fin-S^ {n = n} m)
  Fin-S^-inj O _ _ p = p
  Fin-S^-inj (S n) _ _ p = Fin-S^-inj n _ _ (Fin-S-inj _ _ p)

  Fin-S^'-inj : ∀ {n} m → is-inj (Fin-S^' {n = n} m)
  Fin-S^'-inj O _ _ p = p
  Fin-S^'-inj (S n) _ _ p = Fin-S-inj _ _ (Fin-S^'-inj n _ _ p)

  Fin-S^'-late-≠ : ∀ n {m} (<m : Fin m) → Fin-S^' (S n) <m ≠ Fin-S^' n (m , ltS)
  Fin-S^'-late-≠ n <m p =  Fin-to-≠ <m (ap fst (Fin-S^'-inj n _ _ p))

  Fin-S^'-early-≠ : ∀ n {m} (<m : Fin m) → Fin-S^' n (m , ltS) ≠ Fin-S^' (S n) <m
  Fin-S^'-early-≠ n <m = Fin-S^'-late-≠ n <m ∘ !

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
