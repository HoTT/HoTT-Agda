{-# OPTIONS --without-K #-}

--open import HoTT
open import homotopy.3x3.PushoutPushout
open import homotopy.3x3.Transpose
open import homotopy.3x3.Common

module homotopy.3x3.From {i} (d : Span^2 {i}) where

open Span^2 d
open M d hiding (Pushout^2)
open M (transpose d) using () renaming (A₀∙ to A∙₀; A₂∙ to A∙₂; A₄∙ to A∙₄;
                                        module F₁∙ to F∙₁; f₁∙ to f∙₁;
                                        module F₃∙ to F∙₃; f₃∙ to f∙₃;
                                        v-h-span to h-v-span)
open M using (Pushout^2)

module I∙₀ = PushoutRec {D = Pushout^2 d}
                        (left ∘ left) (right ∘ left) (glue ∘ left)

i∙₀ : A∙₀ → Pushout^2 d
i∙₀ = I∙₀.f

module I∙₄ = PushoutRec {D = Pushout^2 d}
                        (left ∘ right) (right ∘ right) (glue ∘ right)

i∙₄ : A∙₄ → Pushout^2 d
i∙₄ = I∙₄.f

module E∙₂Red (c : A₂₂) where

  lhs-o : _
  lhs-o =
      ap (i∙₄ ∘ f∙₃) (glue c)
         =⟨ ap-∘ i∙₄ f∙₃ (glue c) ⟩
      ap i∙₄ (ap f∙₃ (glue c))
           =⟨ F∙₃.glue-β c |in-ctx (ap i∙₄) ⟩
      ap i∙₄ (ap left (H₁₃ c) ∙ glue (f₂₃ c) ∙ ap right (! (H₃₃ c)))
           =⟨ ap-∙∙!`∘`∘ i∙₄ left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c) ⟩
      ap (left ∘ right) (H₁₃ c) ∙ ap i∙₄ (glue (f₂₃ c)) ∙ ! (ap (right ∘ right) (H₃₃ c))
           =⟨ I∙₄.glue-β (f₂₃ c) |in-ctx (λ u → ap (left ∘ right) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c))) ⟩
      ap (left ∘ right) (H₁₃ c) ∙ glue (right (f₂₃ c)) ∙ ! (ap (right ∘ right) (H₃₃ c)) ∎

  rhs-o : _
  rhs-o =
      ! (ap (left ∘ left) (H₁₁ c)) ∙ glue (left (f₂₁ c)) ∙ ap (right ∘ left) (H₃₁ c)
           =⟨ ! (I∙₀.glue-β (f₂₁ c)) |in-ctx (λ u → (! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c))) ⟩
      ! (ap (left ∘ left) (H₁₁ c)) ∙ ap i∙₀ (glue (f₂₁ c)) ∙ ap (right ∘ left) (H₃₁ c)
           =⟨ ! (ap-!∙∙`∘`∘ i∙₀ left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c)) ⟩
      ap i∙₀ (ap left (! (H₁₁ c)) ∙ glue (f₂₁ c) ∙ ap right (H₃₁ c))
           =⟨ ! (F∙₁.glue-β c) |in-ctx (λ u → ap i∙₀ u) ⟩
      ap i∙₀ (ap f∙₁ (glue c))
           =⟨ ∘-ap i∙₀ f∙₁ (glue c) ⟩
      ap (i∙₀ ∘ f∙₁) (glue c) ∎

  T-lhs : Type _
  T-lhs = right (left (f₃₀ (f₂₁ c))) == right (right (f₃₄ (f₂₃ c))) :> Pushout^2 d

  lhs-i : _ == _ :> T-lhs
  lhs-i =
      ap (right ∘ left) (H₃₁ c) ∙ ap right (glue (f₃₂ c)) ∙ ap (right ∘ right) (H₃₃ c)
        =⟨ ! (ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)) ⟩
      ap right (ap left (H₃₁ c) ∙ glue (f₃₂ c) ∙ ap right (H₃₃ c))
        =⟨ ! (ap (ap right) (F₃∙.glue-β c)) ⟩
      ap right (ap f₃∙ (glue c))
        =⟨ ∘-ap right f₃∙ (glue c) ⟩
      ap (right ∘ f₃∙) (glue c) ∎

  T-rhs : Type _
  T-rhs = left (left (f₁₀ (f₂₁ c))) == left (right (f₁₄ (f₂₃ c))) :> Pushout^2 d

  rhs-i : _ == _ :> T-rhs
  rhs-i =
      ap (left ∘ f₁∙) (glue c)
        =⟨ ap-∘ left f₁∙ (glue c) ⟩
      ap left (ap f₁∙ (glue c))
        =⟨ F₁∙.glue-β c |in-ctx (ap left) ⟩
      ap left (ap left (H₁₁ c) ∙ glue (f₁₂ c) ∙ ap right (H₁₃ c))
        =⟨ ap-∙∙`∘`∘ left left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c) ⟩
      (ap (left ∘ left) (H₁₁ c) ∙ ap left (glue (f₁₂ c)) ∙ ap (left ∘ right) (H₁₃ c)) ∎

  coh! : (p : (_ , _ =□ _ , _)) → _
  coh! = pp-coh! {A = Pushout^2 d}
               {u = glue (left (f₂₁ c))}
               {ap (right ∘ left) (H₃₁ c)}
               {ap right (glue (f₃₂ c))}
               {ap (right ∘ right) (H₃₃ c)}
               {ap (left ∘ left) (H₁₁ c)}
               {ap left (glue (f₁₂ c))}
               {ap (left ∘ right) (H₁₃ c)}
               {glue (right (f₂₃ c))}

  coh : (p : (_ , _ =□ _ , _)) → _
  coh = pp-coh {A = Pushout^2 d}
               {p = ap left (glue (f₁₂ c))}
               {ap (left ∘ right) (H₁₃ c)}
               {glue (right (f₂₃ c))}
               {ap (right ∘ right) (H₃₃ c)}
               {ap (left ∘ left) (H₁₁ c)}
               {glue (left (f₂₁ c))}
               {ap (right ∘ left) (H₃₁ c)}
               {ap right (glue (f₃₂ c))}

  module _ (to : Pushout^2 d → Pushout^2 (transpose d)) where

    ap-ap-coh! : (p : _ , _ =□ _ , _) → _
    ap-ap-coh! = pp-coh!  {u = ap to (glue (left (f₂₁ c)))}
                          {ap (to ∘ right ∘ left) (H₃₁ c)}
                          {ap to (ap right (glue (f₃₂ c)))}
                          {ap (to ∘ right ∘ right) (H₃₃ c)}
                          {ap (to ∘ left ∘ left) (H₁₁ c)}
                          {ap to (ap left (glue (f₁₂ c)))}
                          {ap (to ∘ left ∘ right) (H₁₃ c)}
                          {ap to (glue (right (f₂₃ c)))}

    ap-ap-coh : (p : _ , _ =□ _ , _) → _
    ap-ap-coh = pp-coh {p = ap to (ap left (glue (f₁₂ c)))}
                       {ap (to ∘ left ∘ right) (H₁₃ c)}
                       {ap to (glue (right (f₂₃ c)))}
                       {ap (to ∘ right ∘ right) (H₃₃ c)}
                       {ap (to ∘ left ∘ left) (H₁₁ c)}
                       {ap to (glue (left (f₂₁ c)))}
                       {ap (to ∘ right ∘ left) (H₃₁ c)}
                       {ap to (ap right (glue (f₃₂ c)))}

    ap-ap-coh!-lhs-i : _
    ap-ap-coh!-lhs-i = ! (ap-∙∙`∘`∘ to (right ∘ left) (right ∘ right) (H₃₁ c) (ap right (glue (f₃₂ c))) (H₃₃ c))

    ap-ap-coh!-rhs-i : _
    ap-ap-coh!-rhs-i = ap-∙∙`∘`∘ to (left ∘ left) (left ∘ right) (H₁₁ c) (ap left (glue (f₁₂ c))) (H₁₃ c)

    ap-ap-coh!-lhs-o : _
    ap-ap-coh!-lhs-o = ap-∙∙!'`∘`∘ to (left ∘ right) (right ∘ right) (H₁₃ c) (glue (right (f₂₃ c))) (H₃₃ c)

    ap-ap-coh!-rhs-o : _
    ap-ap-coh!-rhs-o = ! (ap-!'∙∙`∘`∘ to (left ∘ left) (right ∘ left) (H₁₁ c) (glue (left (f₂₁ c))) (H₃₁ c))

    ap-ap-coh!-β : (α : _)
            → ap□ to (coh! α) == ap-ap-coh! (ap□ to α
                                             ∙□-i/ ap-ap-coh!-lhs-i
                                                 / ap-ap-coh!-rhs-i /)
                                 ∙□-i/ ap-ap-coh!-lhs-o
                                     / ap-ap-coh!-rhs-o /
    ap-ap-coh!-β α = ap□-coh! {g₁ = left ∘ right} {right ∘ right} {left ∘ left} {right ∘ left} to
                              {u = glue (left (f₂₁ c))} {H₃₁ c} {ap right (glue (f₃₂ c))} {H₃₃ c}
                              {H₁₁ c} {ap left (glue (f₁₂ c))} {H₁₃ c} {glue (right (f₂₃ c))}
                              α

open E∙₂Red

module E∙₂ = PushoutElim {d = span _ _ _ f₁₂ f₃₂} {P = λ c → i∙₀ (f∙₁ c) == i∙₄ (f∙₃ c)}
  (ap left ∘ glue) (ap right ∘ glue)
  (λ c → ↓-='-in' (coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                          ∙□-i/ lhs-i c / rhs-i c /)
                  ∙□-i/ lhs-o c / rhs-o c /))

e∙₂ : (c : A∙₂) → i∙₀ (f∙₁ c) == i∙₄ (f∙₃ c)
e∙₂ = E∙₂.f

module From = PushoutRec {d = h-v-span} {D = Pushout^2 d}
                       i∙₀ i∙₄ e∙₂

from : Pushout^2 (transpose d) → Pushout^2 d
from = From.f

from-glue-glue-β : (c : A₂₂) → ap↓ (ap from) (apd glue (glue c))
                          == (↓-='-in' (coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                                              ∙□-i/ lhs-i c / rhs-i c /)
                                       ∙□-i/ lhs-o c / rhs-o c /))
                              ◃/ From.glue-β (left (f₁₂ c)) / ! (From.glue-β (right (f₃₂ c))) /
from-glue-glue-β c = ∘'-apd (ap from) glue (glue c)
                   ∙ coh1 {p = apd (ap from ∘ glue) (glue c)} {From.glue-β (right (f₃₂ c))}
                          {From.glue-β (left (f₁₂ c))} {apd e∙₂ (glue c)}
                          (↓-=-out (apd From.glue-β (glue c)))
                   ∙ (E∙₂.glue-β c |in-ctx (λ u → u ◃/ From.glue-β (left (f₁₂ c)) / ! (From.glue-β (right (f₃₂ c)))/))
