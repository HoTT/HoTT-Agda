{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.OrdinaryTheory

{- Useful lemmas concerning the functorial action of C -}

module cohomology.Functor {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT

CF-inverse : (n : ℕ) {X Y : Ptd i} (f : fst (X ∙→ Y)) (g : fst (Y ∙→ X))
  → g ∘ptd f == ptd-idf _ → (CF-hom n f) ∘hom (CF-hom n g) == idhom _
CF-inverse n f g p = ! (CF-comp n g f) ∙ ap (CF-hom  n) p ∙ CF-ident n
