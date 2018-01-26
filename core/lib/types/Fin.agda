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

Fin-prop : ℕ → SubtypeProp ℕ lzero
Fin-prop n = ((_< n) , λ _ → <-is-prop)

abstract
  Fin-is-set : {n : ℕ} → is-set (Fin n)
  Fin-is-set {n} = Subtype-level (Fin-prop n)

Fin-pred=-type : {n : ℕ} → Fin n → Fin n → Type₀
Fin-pred=-type (_ , ltSR _) (_ , ltS) = ⊤
Fin-pred=-type (_ , ltS) (_ , ltSR _) = ⊤
Fin-pred=-type (m , ltS) (n , ltS) = m == n :> ℕ
Fin-pred=-type {S n} (m , ltSR m<n) (o , ltSR o<n) = (m , m<n) == (o , o<n) :> Fin n

Fin-pred= : {n : ℕ} {x y : Fin n} → x == y → Fin-pred=-type x y
Fin-pred= {x = (_ , ltS)} idp = idp
Fin-pred= {x = (_ , ltSR _)} idp = idp

{- This is not made abstract so that certain proofs compute in a certain way.
   Otherwise [Subtype-has-dec-eq (Fin-prop n) ℕ-has-dec-eq] is a shorter proof. -}
Fin-has-dec-eq : {n : ℕ} → has-dec-eq (Fin n)
Fin-has-dec-eq (_ , ltS) (_ , ltS) = inl idp
Fin-has-dec-eq (m , ltS) (o , ltSR o<m) = inr $ <-to-≠ o<m ∘ ! ∘ ap fst
Fin-has-dec-eq (m , ltSR m<o) (o , ltS) = inr $ <-to-≠ m<o ∘ ap fst
Fin-has-dec-eq (_ , ltSR m<n) (_ , ltSR o<n) with Fin-has-dec-eq (_ , m<n) (_ , o<n)
... | inl p = inl (ap Fin-S p)
... | inr ¬p = inr (¬p ∘ Fin-pred=)

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
