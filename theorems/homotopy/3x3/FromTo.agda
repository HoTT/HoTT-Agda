{-# OPTIONS --without-K #-}

--open import HoTT
open import homotopy.3x3.PushoutPushout
open import homotopy.3x3.Transpose
import homotopy.3x3.To as To
import homotopy.3x3.From as From
open import homotopy.3x3.Common

module homotopy.3x3.FromTo {i} (d : Span^2 {i}) where

open Span^2 d
open M d hiding (Pushout^2)
open M (transpose d) using () renaming (module F₁∙ to F∙₁; f₁∙ to f∙₁;
                                        module F₃∙ to F∙₃; f₃∙ to f∙₃;
                                        v-h-span to h-v-span)
open M using (Pushout^2)

open To d
open From d

open import homotopy.3x3.FromToInit d
open import homotopy.3x3.FromTo2 d
open import homotopy.3x3.FromTo3 d

from-to-g-g : (c : A₂₂) → (from-to-g-l (f₂₁ c) , ↓-='-out (apd (from-to-r ∘ f₃∙) (glue c)) , ↓-='-out (apd (ap from ∘ ap to ∘ glue) (glue c))
                        =□□ ↓-='-out (apd glue (glue c)) , ↓-='-out (apd (from-to-l ∘ f₁∙) (glue c)) , from-to-g-r (f₂₃ c))
from-to-g-g c = coh _ lemma1 lemma3 _ _ (↓-='-out (apd glue (glue c))) lemma2
                    where
                open M2 c
                open M3 c


from-to-g-g' : (c : A₂₂) → from-to-g-l (f₂₁ c) == from-to-g-r (f₂₃ c) [ (λ c → (from-to-l (f₁∙ c) , glue c =□ ap from (ap to (glue c)) , from-to-r (f₃∙ c))) ↓ glue c ]
from-to-g-g' c = ↓-=□-in (from-to-g-g c)

module FromToG = PushoutElim {d = span _ _ _ f₂₁ f₂₃} {P = λ c → (from-to-l (f₁∙ c) , glue c =□ ap from (ap to (glue c)) , from-to-r (f₃∙ c))}
                 from-to-g-l from-to-g-r from-to-g-g'

from-to-g : (c : A₂∙) → (from-to-l (f₁∙ c) , glue c =□ ap from (ap to (glue c)) , from-to-r (f₃∙ c))
from-to-g = FromToG.f

from-to-g' : (c : A₂∙) → from-to-l (f₁∙ c) == from-to-r (f₃∙ c) [ (λ z → from (to z) == z) ↓ glue c ]
from-to-g' c = ↓-∘=idf-in' from to (from-to-g c)

from-to : (x : Pushout^2 d) → from (to x) == x
from-to = Pushout-elim from-to-l from-to-r from-to-g'
