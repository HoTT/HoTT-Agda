{-# OPTIONS --without-K #-}

open import Base

module Homotopy.PushoutDef where

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
  {f : C → A} {f' : C' → A'} (s : f' ◯ transport _ r ≡ transport _ p ◯ f)
  {g : C → B} {g' : C' → B'} (t : transport _ q ◯ g ≡ g' ◯ transport _ r)
  → (diag A , B , C , f , g) ≡ (diag A' , B' , C' , f' , g')
pushout-diag-raw-eq (refl _) (refl _) (refl _) (refl _) (refl _) = refl _

pushout-diag-eq : ∀ {i} {A A' : Set i} (p : A ≃ A')
  {B B' : Set i} (q : B ≃ B') {C C' : Set i} (r : C ≃ C')
  {f : C → A} {f' : C' → A'} (s : (a : C) →  f' (π₁ r a) ≡ (π₁ p) (f a))
  {g : C → B} {g' : C' → B'} (t : (b : C) → (π₁ q) (g b) ≡ g' (π₁ r b))
  → (diag A , B , C , f , g) ≡ (diag A' , B' , C' , f' , g')
pushout-diag-eq p q r {f} {f'} s {g} {g'} t = pushout-diag-raw-eq
  (eq-to-path p)
  (eq-to-path q)
  (eq-to-path r)
  (funext (λ a → map f' (trans-X-eq-to-path r a)
                     ∘ (s a ∘ ! (trans-X-eq-to-path p (f a)))))
  (funext (λ b → trans-X-eq-to-path q (g b)
                     ∘ (t b ∘ map g' (! (trans-X-eq-to-path r b)))))

module Pushout {i} {d : pushout-diag i} where

  open pushout-diag d

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
  
open Pushout public hiding (pushout)

pushout : ∀ {i} (d : pushout-diag i) → Set i
pushout d = Pushout.pushout {_} {d}

-- left : ∀ {i} {d : pushout-diag i} → (pushout-diag.A d → pushout d)
-- left {i} {d} = Pushout.left d

-- right : ∀ {i} {d : pushout-diag i} → (pushout-diag.B d → pushout d)
-- right {i} {d} = Pushout.right d

-- glue : ∀ {i} {d : pushout-diag i}
--   → ((c : pushout-diag.C d) → left (pushout-diag.f d c) ≡ right (pushout-diag.g d c))
-- glue {i} {d} = Pushout.glue d
