{-# OPTIONS --without-K #-}

open import Base

module CategoryTheory.PushoutDef where

record pushout-diag (i : Level) : Set (suc i) where
  constructor diag_,_,_,_,_
  field
    A : Set i
    B : Set i
    C : Set i
    f : C → A
    g : C → B


pushout-diag-raw-eq : ∀ {i} {A A' : Set i} (p : A ≡ A')
  {B B' : Set i} (q : B ≡ B') {C C' : Set i} (r : C ≡ C')
  {f : C → A} {f' : C' → A'} (s : transport _ p (transport _ r f) ≡ f')
  {g : C → B} {g' : C' → B'} (t : transport _ q (transport _ r g) ≡ g')
  → (diag A , B , C , f , g) ≡ (diag A' , B' , C' , f' , g')
pushout-diag-raw-eq (refl _) (refl _) (refl _) (refl _) (refl _) = refl _

pushout-diag-eq : ∀ {i} {A A' : Set i} (p : A ≃ A')
  {B B' : Set i} (q : B ≃ B') {C C' : Set i} (r : C ≃ C')
  {f : C → A} {f' : C' → A'} (s : (a : C) →  (π₁ p) (f a) ≡ f' (π₁ r a))
  {g : C → B} {g' : C' → B'} (t : (b : C) → (π₁ q) (g b) ≡ g' (π₁ r b))
  → (diag A , B , C , f , g) ≡ (diag A' , B' , C' , f' , g')
pushout-diag-eq p q r {f' = f'} s {g' = g'} t = pushout-diag-raw-eq
  (eq-to-path p)
  (eq-to-path q)
  (eq-to-path r)
  (funext-dep (λ a → trans-A→X-eq-to-path _ p _ a
                     ∘ (map (π₁ p) (trans-X→A-eq-to-path _ r _ a)
                       ∘ (s (inverse r a)
                       ∘ map f' (inverse-right-inverse r a)))))
  (funext-dep (λ b → trans-A→X-eq-to-path _ q _ b
                     ∘ (map (π₁ q) (trans-X→A-eq-to-path _ r _ b)
                       ∘ (t (inverse r b)
                       ∘ map g' (inverse-right-inverse r b)))))

module Pushout {i} (D : pushout-diag i) where

  open pushout-diag D

  private
    data #pushout : Set i where
      #left : A → #pushout
      #right : B → #pushout
  
  pushout : Set _
  pushout = #pushout
  
  left : A → pushout
  left = #left
  
  right : B → pushout
  right = #right
  
  postulate  -- HIT
    glue : (c : C) → left (f c) ≡ right (g c)
  
  pushout-rec : ∀ {l} (P : pushout → Set l) (left* : (a : A) → P (left a))
    (right* : (b : B) → P (right b))
    (glue* : (c : C) → transport P (glue c) (left* (f c)) ≡ right* (g c))
    → (x : pushout) → P x
  pushout-rec P left* right* glue* (#left y) = left* y
  pushout-rec P left* right* glue* (#right y) = right* y
  
  postulate  -- HIT
    pushout-β-glue : ∀ {l} (P : pushout → Set l) (left* : (a : A) → P (left a))
      (right* : (b : B) → P (right b))
      (glue* : (c : C) → transport P (glue c) (left* (f c)) ≡ right* (g c))
      (c : C)
        → map-dep (pushout-rec {l} P left* right* glue*) (glue c) ≡ glue* c
  
  pushout-rec-nondep : ∀ {l} (D : Set l) (left* : A → D) (right* : B → D)
    (glue* : (c : C) → left* (f c) ≡ right* (g c)) → (pushout → D)
  pushout-rec-nondep D left* right* glue* (#left y) = left* y
  pushout-rec-nondep D left* right* glue* (#right y) = right* y
  
  postulate  -- HIT
    pushout-β-glue-nondep : ∀ {l} (D : Set l) (left* : A → D) (right* : B → D)
      (glue* : (c : C) → left* (f c) ≡ right* (g c)) (c : C)
      → map (pushout-rec-nondep D left* right* glue*) (glue c) ≡ glue* c
  
  --pushout-β-glue-nondep D left* right* glue* c =
  -- map-dep-trivial (pushout-rec-nondep D left* right* glue*) (glue c)
  --  ∘ (whisker-left (! (trans-nondep (glue c) (left* (f c)))) {!!} ∘ {!!})
  
open Pushout public
