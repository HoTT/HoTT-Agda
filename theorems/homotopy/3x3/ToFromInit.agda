{-# OPTIONS --without-K #-}

--open import HoTT
open import homotopy.3x3.PushoutPushout
open import homotopy.3x3.Transpose
import homotopy.3x3.To as To
import homotopy.3x3.From as From
open import homotopy.3x3.Common

module homotopy.3x3.ToFromInit {i} (d : Span^2 {i}) where

open Span^2 d
open M d hiding (Pushout^2)
open M (transpose d) using () renaming (A₀∙ to A∙₀; A₂∙ to A∙₂; A₄∙ to A∙₄;
                                        module F₁∙ to F∙₁; f₁∙ to f∙₁;
                                        module F₃∙ to F∙₃; f₃∙ to f∙₃;
                                        v-h-span to h-v-span)
open M using (Pushout^2)

open To d
open From d

to-from-l-g : (c : A₂₀) → ap (to ∘ from ∘ left) (glue c) == ap left (glue c)
to-from-l-g c =
  ap (to ∘ i∙₀) (glue c)
       =⟨ ap-∘ to i∙₀ (glue c) ⟩
  ap to (ap i∙₀ (glue c))
       =⟨ I∙₀.glue-β c |in-ctx ap to ⟩
  ap to (glue (left c))
       =⟨ To.glue-β (left c) ⟩
  ap left (glue c) ∎

module ToFromL = PushoutElim {d = span _ _ _ f₁₀ f₃₀} {P = λ a → to (from (left a)) == left a}
                 (λ a → idp) (λ b → idp) (λ c → ↓-='-in (! (to-from-l-g c)))

to-from-l : (a : A∙₀) → to (from (left a)) == left a
to-from-l = ToFromL.f

to-from-r-g : (c : A₂₄) → ap (to ∘ from ∘ right) (glue c) == ap right (glue c)
to-from-r-g c =
  ap (to ∘ i∙₄) (glue c)
       =⟨ ap-∘ to i∙₄ (glue c) ⟩
  ap to (ap i∙₄ (glue c))
       =⟨ I∙₄.glue-β c |in-ctx ap to ⟩
  ap to (glue (right c))
       =⟨ To.glue-β (right c) ⟩
  ap right (glue c) ∎

module ToFromR = PushoutElim {d = span _ _ _ f₁₄ f₃₄} {P = λ b → to (from (right b)) == right b}
                 (λ a → idp) (λ b → idp) (λ c → ↓-='-in (! (to-from-r-g c)))

to-from-r : (b : A∙₄) → to (from (right b)) == right b
to-from-r = ToFromR.f

to-from-g-l : (a : A₀₂) → glue (left a) == ap to (ap from (glue (left a)))
to-from-g-l a =
  glue (left a)
       =⟨ ! (I₀∙.glue-β a) ⟩
  ap i₀∙ (glue a)
       =⟨ ap-∘ to left (glue a) ⟩
  ap to (ap left (glue a))
       =⟨ ! (From.glue-β (left a)) |in-ctx ap to ⟩
  ap to (ap from (glue (left a))) ∎

to-from-g-r : (b : A₄₂) → glue (right b) == ap to (ap from (glue (right b)))
to-from-g-r b =
  glue (right b)
       =⟨ ! (I₄∙.glue-β b) ⟩
   ap i₄∙ (glue b)
        =⟨ ap-∘ to right (glue b) ⟩
   ap to (ap right (glue b))
        =⟨ ! (From.glue-β (right b)) |in-ctx ap to ⟩
   ap to (ap from (glue (right b))) ∎
