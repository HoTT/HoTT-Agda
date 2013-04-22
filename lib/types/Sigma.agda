{-# OPTIONS --without-K #-}

open import lib.Basics

module lib.types.Sigma where

-- Cartesian product
_×_ : ∀ {i j} (A : Type i) (B : Type j) → Type (max i j)
A × B = Σ A (λ _ → B)

module _ {i j} {A : Type i} {B : A → Type j} where

  pair : (a : A) (b : B a) → Σ A B
  pair a b = (a , b)

  -- pair= has already been defined

  fst= : {ab a'b' : Σ A B} (p : ab == a'b') → (fst ab == fst a'b')
  fst= {._} {_} idp = idp

  snd= : {ab a'b' : Σ A B} (p : ab == a'b')
    → (snd ab == snd a'b' [ B ↓ fst= p ])
  snd= {._} {_} idp = idp

  fst=-β : {a a' : A} (p : a == a')
    {b : B a} {b' : B a'} (q : b == b' [ B ↓ p ])
    → fst= (pair= p q) == p
  fst=-β idp idp = idp

  snd=-β : {a a' : A} (p : a == a')
    {b : B a} {b' : B a'} (q : b == b' [ B ↓ p ])
    → snd= (pair= p q) == q [ (λ v → b == b' [ B ↓ v ]) ↓ fst=-β p q ]
  snd=-β idp idp = idp

  pair=-η : {ab a'b' : Σ A B} (p : ab == a'b')
    → p == pair= (fst= p) (snd= p)
  pair=-η {._} {_} idp = idp

  -- What’s the type of pair=-ext?

module _ {i j} {A : Type i} {B : A → Type j} where

  Σ= : (x y : Σ A B) → Type (max i j)
  Σ= (a , b) (a' , b') = Σ (a == a') (λ p → b == b' [ B ↓ p ])

  Σ=-eqv : (x y : Σ A B) → (x == y) ≃ (Σ= x y)
  Σ=-eqv x y =
    equiv (λ p → fst= p , snd= p) (λ pq → pair= (fst pq) (snd pq))
          (λ pq → pair= (fst=-β (fst pq) (snd pq)) (snd=-β (fst pq) (snd pq)))
          (λ p → ! (pair=-η p))

  Σ=-path : (x y : Σ A B) → (x == y) == (Σ= x y)
  Σ=-path x y = ua (Σ=-eqv x y)
