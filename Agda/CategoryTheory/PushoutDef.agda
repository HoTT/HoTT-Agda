{-# OPTIONS --without-K #-}

open import Base

module CategoryTheory.PushoutDef {i j k : Level} (A : Set i) (B : Set j)
  (C : Set k) (f : C → A) (g : C → B) where

private
  data #pushout : Set (max i j) where
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
  (glue* : (c : C) → transport P (glue c) (left* (f c)) ≡ right* (g c)) (c : C)
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
