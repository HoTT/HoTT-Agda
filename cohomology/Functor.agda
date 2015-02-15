{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Theory

{- Useful lemmas concerning the functorial action of C -}

module cohomology.Functor {i} (CT : CohomologyTheory i) where

open CohomologyTheory CT

CF-inverse : (n : ℤ) {X Y : Ptd i} (f : fst (X ⊙→ Y)) (g : fst (Y ⊙→ X))
  → g ⊙∘ f == ⊙idf _ → (CF-hom n f) ∘ᴳ (CF-hom n g) == idhom _
CF-inverse n f g p = ! (CF-comp n g f) ∙ ap (CF-hom  n) p ∙ CF-ident n
