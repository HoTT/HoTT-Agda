{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory

{- Useful lemmas concerning the functorial action of C -}

module cohomology.Functor {i} (CT : CohomologyTheory i) where

open CohomologyTheory CT

open import cohomology.Unit CT
open import cohomology.BaseIndependence CT

abstract
  C-fmap-cst : (n : ℤ) {X Y : Ptd i} → ∀ y → CEl-fmap n (⊙cst {X = X} {Y = Y}) y == Cident n X
  C-fmap-cst n {X} {Y} y =
    CEl-fmap n (⊙cst {X = ⊙LU} ⊙∘ ⊙cst {X = X}) y
      =⟨ CEl-fmap-∘ n ⊙cst ⊙cst y ⟩
    CEl-fmap n (⊙cst {X = X}) (CEl-fmap n (⊙cst {X = ⊙LU}) y)
      =⟨ C-Unit n (CEl-fmap n (⊙cst {X = ⊙LU}) y)
         |in-ctx CEl-fmap n (⊙cst {X = X} {Y = ⊙LU}) ⟩
    CEl-fmap n (⊙cst {X = X}) (Cident n ⊙LU)
      =⟨ GroupHom.pres-ident (C-fmap n (⊙cst {X = X} {Y = ⊙LU})) ⟩
    Cident n X ∎
    where
    ⊙LU = ⊙Lift {j = i} ⊙Unit

  C-fmap-const : (n : ℤ) {X Y : Ptd i} {f : X ⊙→ Y}
    → (∀ x → fst f x == pt Y)
    → ∀ y → CEl-fmap n f y == Cident n X
  C-fmap-const n f-is-const y =
    CEl-fmap-base-indep' n f-is-const y ∙ C-fmap-cst n y

  -- FIXME Is there a better name?
  C-fmap-inverse : (n : ℤ) {X Y : Ptd i} (f : X ⊙→ Y) (g : Y ⊙→ X)
    → (∀ x → fst g (fst f x) == x)
    → (∀ x → CEl-fmap n f (CEl-fmap n g x) == x)
  C-fmap-inverse n f g p x = ! (CEl-fmap-∘ n g f x) ∙ CEl-fmap-base-indep' n p x ∙ C-fmap-idf n x

CEl-fmap-cst = C-fmap-cst
CEl-fmap-const = C-fmap-const
CEl-fmap-inverse = C-fmap-inverse
