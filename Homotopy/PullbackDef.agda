{-# OPTIONS --without-K #-}

open import Base

module Homotopy.PullbackDef where

record pullback-diag (i : Level) : Set (suc i) where
  constructor diag_,_,_,_,_
  field
    A : Set i
    B : Set i
    C : Set i
    f : A → C
    g : B → C

pullback-diag-raw-eq : ∀ {i} {A A' : Set i} (p : A ≡ A')
  {B B' : Set i} (q : B ≡ B') {C C' : Set i} (r : C ≡ C')
  {f : A → C} {f' : A' → C'} (s : f' ◯ (transport _ p) ≡ transport _ r ◯ f)
  {g : B → C} {g' : B' → C'} (t : transport _ r ◯ g ≡ g' ◯ (transport _ q))
  → (diag A , B , C , f , g) ≡ (diag A' , B' , C' , f' , g')
pullback-diag-raw-eq (refl _) (refl _) (refl _) (refl _) (refl _) = refl _

pullback-diag-eq : ∀ {i} {A A' : Set i} (p : A ≃ A')
  {B B' : Set i} (q : B ≃ B') {C C' : Set i} (r : C ≃ C')
  {f : A → C} {f' : A' → C'} (s : (a : A) → f' ((π₁ p) a) ≡ (π₁ r) (f a))
  {g : B → C} {g' : B' → C'} (t : (b : B) → (π₁ r) (g b) ≡ g' ((π₁ q) b))
  → (diag A , B , C , f , g) ≡ (diag A' , B' , C' , f' , g')
pullback-diag-eq p q r {f} {f'} s {g} {g'} t = pullback-diag-raw-eq
  (eq-to-path p)
  (eq-to-path q)
  (eq-to-path r)
  (funext-dep (λ a → map f' (trans-X-eq-to-path p a)
                     ∘ (s a ∘ ! (trans-X-eq-to-path r (f a)))))
  (funext-dep (λ b → trans-X-eq-to-path r (g b)
                     ∘ (t b ∘ map g' (! (trans-X-eq-to-path q b)))))

module Pullback {i} (D : pullback-diag i) where

  open pullback-diag D

  record pullback : Set i where
    constructor _,_,_
    field
      a : A
      b : B
      h : f a ≡ g b

  pullback-eq : {a a' : A} (p : a ≡ a') {b b' : B} (q : b ≡ b')
    {h : f a ≡ g b} {h' : f a' ≡ g b'} (r : h ∘ map g q ≡ map f p ∘ h')
    → (a , b , h) ≡ (a' , b' , h')
  pullback-eq (refl _) (refl _) r =
    map (λ u → _ , _ , u) (! (refl-right-unit _) ∘ r)

open Pullback public
