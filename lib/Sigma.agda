{-# OPTIONS --without-K #-}

module lib.Sigma where

open import lib.Base
open import lib.Equivalences
open import lib.Univalence

-- Product
_×_ : ∀ {i j} (A : Type i) (B : Type j) → Type (max i j)
A × B = Σ A (λ _ → B)

module _ {i j} {A : Type i} {B : Type j} where
  pair=' : {a a' : A} (p : a == a') {b b' : B} (q : b == b')
    → (a , b) == (a' , b')
  pair=' idp idp = idp

module _ {i j} {A : Type i} {B : A → Type j} where

  pair : (a : A) (b : B a) → Σ A B
  pair a b = (a , b)

  pair= : {a a' : A} (p : a == a') {b : B a} {b' : B a'}
    (q : b == b' [ B ↓ p ])
    → (a , b) == (a' , b')
  pair= idp idp = idp


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


-- (Un)curryfication
curry : ∀ {i j k} {A : Type i} {B : A → Type j} {C : Σ A B → Type k}
  → (∀ s → C s) → (∀ x y → C (x , y))
curry f x y = f (x , y)

uncurry : ∀ {i j k} {A : Type i} {B : A → Type j} {C : ∀ x → B x → Type k}
  → (∀ x y → C x y) → (∀ s → C (fst s) (snd s))
uncurry f (x , y) = f x y

-- (Un)curryfication with the first argument made implicit
curryi : ∀ {i j k} {A : Type i} {B : A → Type j} {C : Σ A B → Type k}
  → (∀ s → C s) → (∀ {x} y → C (x , y))
curryi f y = f (_ , y)

uncurryi : ∀ {i j k} {A : Type i} {B : A → Type j} {C : ∀ x → B x → Type k}
  → (∀ {x} y → C x y) → (∀ s → C (fst s) (snd s))
uncurryi f (x , y) = f y
