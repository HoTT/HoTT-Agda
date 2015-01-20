{-# OPTIONS --without-K #-}

--open import HoTT
open import homotopy.3x3.PushoutPushout
open import homotopy.3x3.Transpose
import homotopy.3x3.To as To
import homotopy.3x3.From as From
open import homotopy.3x3.Common

module homotopy.3x3.ToFrom {i} (d : Span^2 {i}) where

open Span^2 d
open M d hiding (Pushout^2)
open M (transpose d) using () renaming (A₀∙ to A∙₀; A₂∙ to A∙₂; A₄∙ to A∙₄;
                                        module F₁∙ to F∙₁; f₁∙ to f∙₁;
                                        module F₃∙ to F∙₃; f₃∙ to f∙₃;
                                        v-h-span to h-v-span)
open M using (Pushout^2)

open To d
open From d

open import homotopy.3x3.ToFromInit d
open import homotopy.3x3.ToFrom2 d
open import homotopy.3x3.ToFrom3 d

to-from-g-g : (c : A₂₂) → (to-from-g-l (f₁₂ c) , ↓-='-out (apd (to-from-r ∘ f∙₃) (glue c)) , ↓-='-out (apd (ap to ∘ ap from ∘ glue) (glue c))
                        =□□ ↓-='-out (apd glue (glue c)) , ↓-='-out (apd (to-from-l ∘ f∙₁) (glue c)) , to-from-g-r (f₃₂ c))
to-from-g-g c = coh _ lemma1 lemma3 _ _ (↓-='-out (apd glue (glue c))) lemma2
                    where
                open M2 c
                open M3 c

to-from-g-g' : (c : A₂₂) → to-from-g-l (f₁₂ c) == to-from-g-r (f₃₂ c) [ (λ c → (to-from-l (f∙₁ c) , glue c =□ ap to (ap from (glue c)) , to-from-r (f∙₃ c))) ↓ glue c ]
to-from-g-g' c = ↓-=□-in (to-from-g-g c)

module ToFromG = PushoutElim {d = span _ _ _ f₁₂ f₃₂} {P = λ c → (to-from-l (f∙₁ c) , glue c =□ ap to (ap from (glue c)) , to-from-r (f∙₃ c))}
                 to-from-g-l to-from-g-r to-from-g-g'

to-from-g : (c : A∙₂) → (to-from-l (f∙₁ c) , glue c =□ ap to (ap from (glue c)) , to-from-r (f∙₃ c))
to-from-g = ToFromG.f

to-from-g' : (c : A∙₂) → to-from-l (f∙₁ c) == to-from-r (f∙₃ c) [ (λ z → to (from z) == z) ↓ glue c ]
to-from-g' c = ↓-∘=idf-in to from (to-from-g c)

to-from : (x : Pushout^2 (transpose d)) → to (from x) == x
to-from = Pushout-elim to-from-l to-from-r to-from-g'
