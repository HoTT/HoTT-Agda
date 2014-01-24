{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Group
open import lib.types.Sigma

module cohomology.GroupProduct where

×-group-struct : ∀ {i j} {A : Type i} {B : Type j} 
  (GS : GroupStructure A) (HS : GroupStructure B)
  → GroupStructure (A × B)
×-group-struct GS HS = record {
  ident = (ident GS , ident HS);
  inv = λ {(g , h) → (inv GS g , inv HS h)};
  comp = λ {(g₁ , h₁) (g₂ , h₂) → (comp GS g₁ g₂ , comp HS h₁ h₂)};
  unitl = λ {(g , h) → pair×= (unitl GS g) (unitl HS h)};
  unitr = λ {(g , h) → pair×= (unitr GS g) (unitr HS h)};
  assoc = λ {(g₁ , h₁) (g₂ , h₂) (g₃ , h₃) → 
    pair×= (assoc GS g₁ g₂ g₃) (assoc HS h₁ h₂ h₃)};
  invl = λ {(g , h) → pair×= (invl GS g) (invl HS h)};
  invr = λ {(g , h) → pair×= (invr GS g) (invr HS h)}}
  where open GroupStructure

_×G_ : ∀ {i j} → Group i → Group j → Group (lmax i j)
_×G_ (group A A-level A-struct) (group B B-level B-struct) = 
  group (A × B) (×-level A-level B-level) (×-group-struct A-struct B-struct)
