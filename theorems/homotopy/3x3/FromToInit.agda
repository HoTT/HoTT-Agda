{-# OPTIONS --without-K --rewriting #-}

--open import HoTT
open import homotopy.3x3.PushoutPushout
open import homotopy.3x3.Transpose
import homotopy.3x3.To as To
import homotopy.3x3.From as From
open import homotopy.3x3.Common

module homotopy.3x3.FromToInit {i} (d : Span^2 {i}) where

open Span^2 d
open M d hiding (Pushout^2)
open M (transpose d) using () renaming (module F₁∙ to F∙₁; f₁∙ to f∙₁;
                                        module F₃∙ to F∙₃; f₃∙ to f∙₃;
                                        v-h-span to h-v-span)
open M using (Pushout^2)

open To d
open From d

from-to-l-g : (c : A₀₂) → ap (from ∘ to ∘ left) (glue c) == ap left (glue c)
from-to-l-g c =
  ap (from ∘ i₀∙) (glue c)
       =⟨ ap-∘ from i₀∙ (glue c) ⟩
  ap from (ap i₀∙ (glue c))
       =⟨ I₀∙.glue-β c |in-ctx ap from ⟩
  ap from (glue (left c))
       =⟨ From.glue-β (left c) ⟩
  ap left (glue c) ∎

module FromToL = PushoutElim {d = span _ _ _ f₀₁ f₀₃} {P = λ a → from (to (left a)) == left a}
                 (λ a → idp) (λ b → idp) (λ c → ↓-='-in' (! (from-to-l-g c)))

from-to-l : (a : A₀∙) → from (to (left a)) == left a
from-to-l = FromToL.f

from-to-r-g : (c : A₄₂) → ap (from ∘ to ∘ right) (glue c) == ap right (glue c)
from-to-r-g c =
  ap (from ∘ i₄∙) (glue c)
       =⟨ ap-∘ from i₄∙ (glue c) ⟩
  ap from (ap i₄∙ (glue c))
       =⟨ I₄∙.glue-β c |in-ctx ap from ⟩
  ap from (glue (right c))
       =⟨ From.glue-β (right c) ⟩
  ap right (glue c) ∎

module FromToR = PushoutElim {d = span _ _ _ f₄₁ f₄₃} {P = λ b → from (to (right b)) == right b}
                 (λ a → idp) (λ b → idp) (λ c → ↓-='-in' (! (from-to-r-g c)))

from-to-r : (b : A₄∙) → from (to (right b)) == right b
from-to-r = FromToR.f

from-to-g-l : (a : A₂₀) → glue (left a) == ap from (ap to (glue (left a)))
from-to-g-l a =
  glue (left a)
       =⟨ ! (I∙₀.glue-β a) ⟩
  ap i∙₀ (glue a)
       =⟨ ap-∘ from left (glue a) ⟩
  ap from (ap left (glue a))
       =⟨ ! (To.glue-β (left a)) |in-ctx ap from ⟩
  ap from (ap to (glue (left a))) ∎

from-to-g-r : (b : A₂₄) → glue (right b) == ap from (ap to (glue (right b)))
from-to-g-r b =
  glue (right b)
       =⟨ ! (I∙₄.glue-β b) ⟩
   ap i∙₄ (glue b)
        =⟨ ap-∘ from right (glue b) ⟩
   ap from (ap right (glue b))
        =⟨ ! (To.glue-β (right b)) |in-ctx ap from ⟩
   ap from (ap to (glue (right b))) ∎
