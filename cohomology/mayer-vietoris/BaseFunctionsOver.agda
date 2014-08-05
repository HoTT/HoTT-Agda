{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.CofiberSequence
open import cohomology.FunctionOver

module cohomology.mayer-vietoris.BaseFunctionsOver {i} {A B : Type i}
  (Z : Ptd i) (f : fst Z → A) (g : fst Z → B) where

open import cohomology.mayer-vietoris.BaseEquivMaps Z f g
open import cohomology.mayer-vietoris.BaseEquivalence Z f g
open import cohomology.mayer-vietoris.Functions ps

base-cfcod-over : ptd-cfcod ptd-reglue == ptd-extract-glue
       [ (λ W → fst (Ptd-Pushout ps ∙→ W)) ↓ base-ptd-path ]
base-cfcod-over =
  codomain-over-ptd-equiv (ptd-cfcod ptd-reglue) base-equiv idp ▹ lemma
  where
  lemma : (into , idp) ∘ptd ptd-cfcod ptd-reglue == ptd-extract-glue
  lemma = pair= idp $
    ap into (! (cfglue reglue (winl (snd X)))) ∙ idp
      =⟨ ap-! into (cfglue reglue (winl (snd X))) |in-ctx (λ w → w ∙ idp) ⟩
    ! (ap into (cfglue reglue (winl (snd X)))) ∙ idp
      =⟨ Into.glue-β (winl (snd X)) |in-ctx (λ w → ! w ∙ idp) ⟩
    idp ∎

{- to add: effect on co∂ ? -}
