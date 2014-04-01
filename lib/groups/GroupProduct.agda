{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Group
open import lib.types.Sigma
open import lib.types.Pi

module lib.groups.GroupProduct where

{- binary product -}
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


{- general product -}
Π-group-struct : ∀ {i j} {I : Type i} {A : I → Type j}
  (FS : (i : I) → GroupStructure (A i))
  → GroupStructure (Π I A)
Π-group-struct FS = record {
  ident = ident ∘ FS;
  inv = λ f i → inv (FS i) (f i);
  comp = λ f g i → comp (FS i) (f i) (g i);
  unitl = λ f → (λ= (λ i → unitl (FS i) (f i)));
  unitr = λ f → (λ= (λ i → unitr (FS i) (f i)));
  assoc = λ f g h → (λ= (λ i → assoc (FS i) (f i) (g i) (h i)));
  invl = λ f → (λ= (λ i → invl (FS i) (f i)));
  invr = λ f → (λ= (λ i → invr (FS i) (f i)))}
  where open GroupStructure

ΠG : ∀ {i j} (I : Type i) (F : I → Group j) → Group (lmax i j)
ΠG I F = group (Π I (El ∘ F)) (Π-level (λ i → El-level (F i))) 
               (Π-group-struct (group-struct ∘ F))
  where open Group


{- defining a homomorphism into a binary product -}
×-hom : ∀ {i j k} {G : Group i} {H : Group j} {K : Group k}
  → GroupHom G H → GroupHom G K → GroupHom G (H ×G K)
×-hom (group-hom h h-id h-comp) (group-hom k k-id k-comp) = record {
  f = λ x → (h x , k x);
  pres-ident = pair×= h-id k-id;
  pres-comp = λ x y → pair×= (h-comp x y) (k-comp x y)}

