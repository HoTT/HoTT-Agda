{-# OPTIONS --without-K #-}

--open import HoTT
open import homotopy.3x3.PushoutPushout
open import homotopy.3x3.Transpose
import homotopy.3x3.To as To
import homotopy.3x3.From as From
open import homotopy.3x3.Common

module homotopy.3x3.ToFrom3 {i} (d : Span^2 {i}) where

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

module M3 (c : A₂₂) where

  open M2 c

  lemma2-3 =
    ap□ to (E∙₂Red.coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                            ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /)
              ∙□-i/ E∙₂Red.lhs-o c / E∙₂Red.rhs-o c /)

         =⟨ ap□-∙□-i/ to _ (E∙₂Red.lhs-o c) (E∙₂Red.rhs-o c) ⟩

    ap□ to (E∙₂Red.coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                            ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /))
    ∙□-i/ ap (ap to) (E∙₂Red.lhs-o c) / ap (ap to) (E∙₂Red.rhs-o c) /

         =⟨ lemma2-4 |in-ctx (λ u → u ∙□-i/ ap (ap to) (E∙₂Red.lhs-o c) / ap (ap to) (E∙₂Red.rhs-o c) /) ⟩

    ↓-='-out (apd (glue {d = h-v-span}) (glue c))
    ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /
    ∙□-o/ ∘-ap to left (glue (f₁₂ c)) ∙ I₀∙.glue-β (f₁₂ c) / ! (∘-ap to right (glue (f₃₂ c)) ∙ I₄∙.glue-β (f₃₂ c)) /
    ∙□-i/ (To.glue-β (right (f₂₃ c))) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c)))
        / (! (To.glue-β (left (f₂₁ c)))) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (left ∘ right) (H₃₁ c)) /
    ∙□-i/ E∙₂Red.ap-ap-coh!-lhs-o c to / E∙₂Red.ap-ap-coh!-rhs-o c to /
    ∙□-i/ ap (ap to) (E∙₂Red.lhs-o c) / ap (ap to) (E∙₂Red.rhs-o c) / ∎

  lemma2'-3 =
    ap-∘ to (i∙₄ ∘ f∙₃) (glue c)
    ∙ ap (ap to) (E∙₂Red.lhs-o c)
    ∙ E∙₂Red.ap-ap-coh!-lhs-o c to
    ∙ ((To.glue-β (right (f₂₃ c))) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c))))
    ∙ E₂∙Red.lhs-i c

      =⟨ coh2 (ap to)
              (ap-∘ to (i∙₄ ∘ f∙₃) (glue c))
              (ap-∘ i∙₄ f∙₃ (glue c))
              _
              _
              _
              (ap-∙∙!'`∘`∘ to (left ∘ right) (right ∘ right) (H₁₃ c) (glue (right (f₂₃ c))) (H₃₃ c))
              ((To.glue-β (right (f₂₃ c))) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c))))
              (! (ap-∙∙!`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c)))
              (ap-! (ap right) (F∙₃.glue-β c))
              _
              ⟩

    (ap-∘ to (i∙₄ ∘ f∙₃) (glue c)
     ∙ ap (ap to) (ap-∘ i∙₄ f∙₃ (glue c))
     ∙ ap (ap to) (F∙₃.glue-β c |in-ctx (ap i∙₄)))
    ∙ (ap (ap to) (ap-∙∙!`∘`∘ i∙₄ left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c))
       ∙ ap (ap to) (I∙₄.glue-β (f₂₃ c) |in-ctx (λ u → ap (left ∘ right) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c))))
       ∙ ap-∙∙!'`∘`∘ to (left ∘ right) (right ∘ right) (H₁₃ c) (glue (right (f₂₃ c))) (H₃₃ c))
    ∙ (((To.glue-β (right (f₂₃ c))) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c))))
       ∙ ! (ap-∙∙!`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c))
       ∙ ! (ap (ap right) (F∙₃.glue-β c))
       ∙ ∘-ap right f∙₃ (glue c))

      =⟨ ap-∘-ap-∙∙!'2`∘`∘-coh to i∙₄ left right (H₁₃ c) (I∙₄.glue-β (f₂₃ c)) (H₃₃ c)
         |in-ctx (λ u → (ap-∘ to (i∙₄ ∘ f∙₃) (glue c)
                         ∙ ap (ap to) (ap-∘ i∙₄ f∙₃ (glue c))
                         ∙ ap (ap to) (F∙₃.glue-β c |in-ctx (ap i∙₄)))
                        ∙ u
                        ∙ (((To.glue-β (right (f₂₃ c))) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c))))
                           ∙ ! (ap-∙∙!`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c))
                           ∙ ! (ap (ap right) (F∙₃.glue-β c))
                           ∙ ∘-ap right f∙₃ (glue c))) ⟩

    (ap-∘ to (i∙₄ ∘ f∙₃) (glue c)
     ∙ ap (ap to) (ap-∘ i∙₄ f∙₃ (glue c))
     ∙ ap (ap to) (F∙₃.glue-β c |in-ctx (ap i∙₄)))
    ∙ (ap (ap to) (ap-∙∙`∘`∘ i∙₄ left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c)))
       ∙ ap (ap to) (I∙₄.glue-β (f₂₃ c) |in-ctx (λ u → ap (left ∘ right) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
       ∙ ap-∙∙!`∘`∘ to (left ∘ right) (right ∘ right) (H₁₃ c) (glue (right (f₂₃ c))) (H₃₃ c))
    ∙ (((To.glue-β (right (f₂₃ c))) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c))))
       ∙ ! (ap-∙∙!`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c))
       ∙ ! (ap (ap right) (F∙₃.glue-β c))
       ∙ ∘-ap right f∙₃ (glue c))

      =⟨ coh5 (ap-∘ to (i∙₄ ∘ f∙₃) (glue c)
                ∙ ap (ap to) (ap-∘ i∙₄ f∙₃ (glue c))
                ∙ ap (ap to) (F∙₃.glue-β c |in-ctx (ap i∙₄)))
               (ap (ap to) (ap-∙∙`∘`∘ i∙₄ left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c))))
               (ap (ap to) (I∙₄.glue-β (f₂₃ c) |in-ctx (λ u → ap (left ∘ right) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c)))))
               (ap-∙∙!`∘`∘ to (left ∘ right) (right ∘ right) (H₁₃ c) (glue (right (f₂₃ c))) (H₃₃ c))
               ((To.glue-β (right (f₂₃ c))) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c))))
               (! (ap-∙∙!`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c)))
               (! (ap (ap right) (F∙₃.glue-β c)) ∙ ∘-ap right f∙₃ (glue c))

               (ap-∙∙`∘`∘ to (left ∘ right) (right ∘ right) (H₁₃ c) (glue (right (f₂₃ c))) (! (H₃₃ c)))
               ((To.glue-β (right (f₂₃ c))) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
               (! (ap-∙∙`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c))))
               (ap-! (right ∘ right) (H₃₃ c) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ ap right (glue (f₂₃ c)) ∙ u))
               (ap-∙∙!`∘`∘-coh1 to (left ∘ right) (right ∘ right) (H₁₃ c) (To.glue-β (right (f₂₃ c))) (H₃₃ c))
               (ap-∙∙!`∘`∘-coh2 right left right (H₁₃ c) {glue (f₂₃ c)} (H₃₃ c))
          ⟩

    (ap-∘ to (i∙₄ ∘ f∙₃) (glue c)
     ∙ ap (ap to) (ap-∘ i∙₄ f∙₃ (glue c))
     ∙ ap (ap to) (F∙₃.glue-β c |in-ctx (ap i∙₄)))
    ∙ (ap (ap to) (ap-∙∙`∘`∘ i∙₄ left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c)))
       ∙ ap (ap to) (I∙₄.glue-β (f₂₃ c) |in-ctx (λ u → ap (left ∘ right) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
       ∙ ap-∙∙`∘`∘ to (left ∘ right) (right ∘ right) (H₁₃ c) (glue (right (f₂₃ c))) (! (H₃₃ c)))
    ∙ (((To.glue-β (right (f₂₃ c))) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
       ∙ ! (ap-∙∙`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c)))
       ∙ ! (ap (ap right) (F∙₃.glue-β c))
       ∙ ∘-ap right f∙₃ (glue c))

         =⟨ ap-∘-ap-∙∙`∘`∘-coh to i∙₄ left right (H₁₃ c) (I∙₄.glue-β (f₂₃ c)) (! (H₃₃ c))
            |in-ctx (λ u →
              (ap-∘ to (i∙₄ ∘ f∙₃) (glue c)
               ∙ ap (ap to) (ap-∘ i∙₄ f∙₃ (glue c))
               ∙ ap (ap to) (F∙₃.glue-β c |in-ctx (ap i∙₄)))
              ∙ u
              ∙ (((To.glue-β (right (f₂₃ c))) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
                 ∙ ! (ap-∙∙`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c)))
                 ∙ ! (ap (ap right) (F∙₃.glue-β c))
                 ∙ ∘-ap right f∙₃ (glue c))) ⟩

    (ap-∘ to (i∙₄ ∘ f∙₃) (glue c)
     ∙ ap (ap to) (ap-∘ i∙₄ f∙₃ (glue c))
     ∙ ap (ap to) (F∙₃.glue-β c |in-ctx (ap i∙₄)))
    ∙ (∘-ap to i∙₄ (ap left (H₁₃ c) ∙ glue (f₂₃ c) ∙ ap right (! (H₃₃ c)))
       ∙ ap-∙∙`∘`∘ (to ∘ i∙₄) left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c))
       ∙ (ap-∘ to i∙₄ (glue (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
       ∙ (ap (ap to) (I∙₄.glue-β (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c)))))
    ∙ (((To.glue-β (right (f₂₃ c))) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
       ∙ (! (ap-∙∙`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c))))
       ∙ ! (ap (ap right) (F∙₃.glue-β c))
       ∙ ∘-ap right f∙₃ (glue c))

         =⟨ coh3 (ap-∘ to (i∙₄ ∘ f∙₃) (glue c))
                 (ap (ap to) (ap-∘ i∙₄ f∙₃ (glue c)))
                 (ap (ap to) (F∙₃.glue-β c |in-ctx (ap i∙₄)))
                 (∘-ap to i∙₄ (ap left (H₁₃ c) ∙ glue (f₂₃ c) ∙ ap right (! (H₃₃ c))))
                 _
                 _ ⟩

    (ap-∘ to (i∙₄ ∘ f∙₃) (glue c)
     ∙ ap (ap to) (ap-∘ i∙₄ f∙₃ (glue c))
     ∙ ap (ap to) (F∙₃.glue-β c |in-ctx (ap i∙₄))
     ∙ ∘-ap to i∙₄ (ap left (H₁₃ c) ∙ glue (f₂₃ c) ∙ ap right (! (H₃₃ c))))
    ∙ (ap-∙∙`∘`∘ (to ∘ i∙₄) left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c))
       ∙ (ap-∘ to i∙₄ (glue (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
       ∙ (ap (ap to) (I∙₄.glue-β (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c)))))
    ∙ ((To.glue-β (right (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
       ∙ ! (ap-∙∙`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c)))
       ∙ ! (ap (ap right) (F∙₃.glue-β c))
       ∙ ∘-ap right f∙₃ (glue c))

         =⟨ ap-∘-coh to i∙₄ f∙₃ (glue c) (F∙₃.glue-β c)
           |in-ctx (λ u → u ∙ (ap-∙∙`∘`∘ (to ∘ i∙₄) left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c))
                               ∙ (ap-∘ to i∙₄ (glue (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
                               ∙ (ap (ap to) (I∙₄.glue-β (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c)))))
                            ∙ ((To.glue-β (right (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
                               ∙ ! (ap-∙∙`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c)))
                               ∙ ! (ap (ap right) (F∙₃.glue-β c))
                               ∙ ∘-ap right f∙₃ (glue c))) ⟩

    (ap-∘ (to ∘ i∙₄) f∙₃ (glue c)
     ∙ (ap (ap (to ∘ i∙₄)) (F∙₃.glue-β c)))
    ∙ (ap-∙∙`∘`∘ (to ∘ i∙₄) left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c))
       ∙ (ap-∘ to i∙₄ (glue (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
       ∙ (ap (ap to) (I∙₄.glue-β (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c)))))
    ∙ ((To.glue-β (right (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
       ∙ ! (ap-∙∙`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c)))
       ∙ ! (ap (ap right) (F∙₃.glue-β c))
       ∙ ∘-ap right f∙₃ (glue c))

      =⟨ !-ap-∘-inv right f∙₃ (glue c)
          |in-ctx (λ u → (ap-∘ (to ∘ i∙₄) f∙₃ (glue c)
     ∙ (ap (ap (to ∘ i∙₄)) (F∙₃.glue-β c)))
    ∙ (ap-∙∙`∘`∘ (to ∘ i∙₄) left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c))
       ∙ (ap-∘ to i∙₄ (glue (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
       ∙ (ap (ap to) (I∙₄.glue-β (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c)))))
    ∙ ((To.glue-β (right (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
       ∙ ! (ap-∙∙`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c)))
       ∙ ! (ap (ap right) (F∙₃.glue-β c))
       ∙ u)) ⟩

    (ap-∘ (to ∘ i∙₄) f∙₃ (glue c)
     ∙ (ap (ap (to ∘ i∙₄)) (F∙₃.glue-β c)))
    ∙ (ap-∙∙`∘`∘ (to ∘ i∙₄) left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c))
       ∙ (ap-∘ to i∙₄ (glue (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
       ∙ (ap (ap to) (I∙₄.glue-β (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c)))))
    ∙ ((To.glue-β (right (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
       ∙ ! (ap-∙∙`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c)))
       ∙ ! (ap (ap right) (F∙₃.glue-β c))
       ∙ ! (ap-∘ right f∙₃ (glue c)))

      =⟨ !-∘-ap-inv (to ∘ i∙₄) f∙₃ (glue c)
         |in-ctx (λ u → (u
     ∙ (ap (ap (to ∘ i∙₄)) (F∙₃.glue-β c)))
    ∙ (ap-∙∙`∘`∘ (to ∘ i∙₄) left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c))
       ∙ (ap-∘ to i∙₄ (glue (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
       ∙ (ap (ap to) (I∙₄.glue-β (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c)))))
    ∙ ((To.glue-β (right (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
       ∙ ! (ap-∙∙`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c)))
       ∙ ! (ap (ap right) (F∙₃.glue-β c))
       ∙ ! (ap-∘ right f∙₃ (glue c)))) ⟩

    (! (∘-ap (to ∘ i∙₄) f∙₃ (glue c))
     ∙ (ap (ap (to ∘ i∙₄)) (F∙₃.glue-β c)))
    ∙ (ap-∙∙`∘`∘ (to ∘ i∙₄) left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c))
       ∙ (ap-∘ to i∙₄ (glue (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
       ∙ (ap (ap to) (I∙₄.glue-β (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c)))))
    ∙ ((To.glue-β (right (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
       ∙ ! (ap-∙∙`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c)))
       ∙ ! (ap (ap right) (F∙₃.glue-β c))
       ∙ ! (ap-∘ right f∙₃ (glue c)))

      =⟨ coh4 (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c)))
               (∘-ap (to ∘ i∙₄) f∙₃ (glue c)) _ _ _ _ _ _ _ _ ⟩

    ! end-lemma1 ∎  where

      coh2 : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {a b c d e : A} {g h k l m n : B}
        (p : g == f a) (q : a == b) (r : b == c) (s : c == d) (t : d == e) (u : f e == h) (v : h == k)
        (w : k == l) {x x' : l == m} (eq-x : x == x') (y : m == n)
        → p ∙ ap f (_ =⟨ q ⟩ _ =⟨ r ⟩ _ =⟨ s ⟩ _ =⟨ t ⟩ _ ∎) ∙ u ∙ v ∙ (_ =⟨ w ⟩ _ =⟨ x ⟩ _ =⟨ y ⟩ _ ∎)
          == (p ∙ ap f q ∙ ap f r) ∙ (ap f s ∙ ap f t ∙ u) ∙ (v ∙ w ∙ x' ∙ y)
      coh2 f p idp idp idp idp idp idp idp {x = idp} idp idp = ! (∙-unit-r (p ∙ idp))

      coh3 : ∀ {i} {A : Type i} {a b c d e f g : A} (p : a == b) (q : b == c) (r : c == d) (s : d == e)
        (t : e == f) (u : f == g)
        → (p ∙ q ∙ r) ∙ (s ∙ t) ∙ u == (p ∙ q ∙ r ∙ s) ∙ t ∙ u
      coh3 idp idp idp idp idp idp = idp

      coh4 : ∀ {i j} {A : Type i} {B : Type j} (h : A → B)
        {a b c d : A} {e f g k l m : B} (p : f == e) (q : f == g) (r : g == h a) (s : a == b) (t : b == c)
        (u : c == d) (v : k == h d) (w : l == k) (x : m == l)
        → (! p ∙ q) ∙ (r ∙ (s |in-ctx h) ∙ (t |in-ctx h)) ∙ ((u |in-ctx h) ∙ (! v) ∙ (! w) ∙ ! x)
          == ! (_ =⟨ x ⟩ _ =⟨ w ⟩ _ =⟨ v ⟩ _ =⟨ ! (_ =⟨ s ⟩ _ =⟨ t ⟩ _ =⟨ u ⟩ _ ∎) |in-ctx h ⟩ _ =⟨ ! r ⟩ _ =⟨ ! q ⟩ _ =⟨ p ⟩ _ ∎)
      coh4 h idp idp r idp idp idp v idp idp = ch r v  where

        ch : ∀ {i} {B : Type i} {a b c : B} (r : a == b) (v : c == b)
           → (r ∙ idp) ∙ ! v ∙ idp == ! (_ =⟨ idp ⟩ _ =⟨ idp ⟩ _ =⟨ v ⟩ _ =⟨ idp ⟩ _ =⟨ ! r ⟩ _ ∎)
        ch idp idp = idp

      coh5 : ∀ {i} {A : Type i} {a b c d e e' f f' g h : A} (p : a == b) (q : b == c)
        (r : c == d) (s : d == e) (t : e == f) (u : f == g) (v : g == h) (s' : d == e')
        (t' : e' == f') (u' : f' == g) (w : f' == f) (α : s ∙ t == s' ∙ t' ∙ w) (β : w ∙ u == u')
        → p ∙ (q ∙ r ∙ s) ∙ (t ∙ u ∙ v)
          == p ∙ (q ∙ r ∙ s') ∙ (t' ∙ u' ∙ v)
      coh5 idp idp idp idp idp idp idp idp idp ._ ._ idp idp = idp

  lemma2'-4 =
    E₂∙Red.rhs-i c
    ∙ ((! (To.glue-β (left (f₂₁ c)))) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (left ∘ right) (H₃₁ c)))
    ∙ E∙₂Red.ap-ap-coh!-rhs-o c to
    ∙ ap (ap to) (E∙₂Red.rhs-o c)
    ∙ ∘-ap to (i∙₀ ∘ f∙₁) (glue c)

      =⟨ coh2 (ap to)
           (ap-∘ left f∙₁ (glue c))
           (F∙₁.glue-β c |in-ctx (ap left))
           (ap-!∙∙`∘`∘ left left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c))
           ((! (To.glue-β (left (f₂₁ c)))) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (left ∘ right) (H₃₁ c)))
           (ap-∘ to (i∙₀ ∘ f∙₁) (glue c))
           (ap-∘ i∙₀ f∙₁ (glue c))
           ((F∙₁.glue-β c) |in-ctx ap i∙₀)
           (ap-!∙∙`∘`∘ i∙₀ left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c))
           ((I∙₀.glue-β (f₂₁ c)) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c)))
           (ap-!'∙∙`∘`∘ to (left ∘ left) (right ∘ left) (H₁₁ c) (glue (left (f₂₁ c))) (H₃₁ c))
           (!-ap (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c)) (I∙₀.glue-β (f₂₁ c)))
           (!-ap (ap i∙₀) (F∙₁.glue-β c))
           (!-ap-∘ i∙₀ f∙₁ (glue c))
           (!-∘-ap to (i∙₀ ∘ f∙₁) (glue c)) ⟩

    ap-∘ left f∙₁ (glue c)
    ∙ (F∙₁.glue-β c |in-ctx (ap left))
    ∙ (ap-!∙∙`∘`∘ left left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c))
    ∙ ((! (To.glue-β (left (f₂₁ c)))) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (left ∘ right) (H₃₁ c)))
    ∙ ! ((ap-∘ to (i∙₀ ∘ f∙₁) (glue c)
          ∙ ap (ap to) (ap-∘ i∙₀ f∙₁ (glue c))
          ∙ ap (ap to) ((F∙₁.glue-β c) |in-ctx (λ u → ap i∙₀ u)))
         ∙ (ap (ap to) (ap-!∙∙`∘`∘ i∙₀ left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c))
            ∙ ap (ap to) ((I∙₀.glue-β (f₂₁ c)) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c)))
            ∙ ap-!'∙∙`∘`∘ to (left ∘ left) (right ∘ left) (H₁₁ c) (glue (left (f₂₁ c))) (H₃₁ c)))

      =⟨ lm |in-ctx (λ u →
    ap-∘ left f∙₁ (glue c)
    ∙ ap (ap left) (F∙₁.glue-β c)
    ∙ ap-!∙∙`∘`∘ left left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c)
    ∙ ((! (To.glue-β (left (f₂₁ c)))) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (left ∘ right) (H₃₁ c)))
    ∙ ! u) ⟩

    ap-∘ left f∙₁ (glue c)
    ∙ (F∙₁.glue-β c |in-ctx (ap left))
    ∙ ap-!∙∙`∘`∘ left left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c)
    ∙ ((! (To.glue-β (left (f₂₁ c)))) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (left ∘ right) (H₃₁ c)))
    ∙ ! ((ap-∘ (to ∘ i∙₀) f∙₁ (glue c)
          ∙ ap (ap (to ∘ i∙₀)) (F∙₁.glue-β c))
         ∙ (ap-∙∙`∘`∘ (to ∘ i∙₀) left right (! (H₁₁ c)) (glue (f₂₁ c)) (H₃₁ c)
            ∙ (ap-∘ to i∙₀ (glue (f₂₁ c)) |in-ctx (λ u → ap (left ∘ left) (! (H₁₁ c)) ∙ u ∙ ap (left ∘ right) (H₃₁ c)))
            ∙ ((I∙₀.glue-β (f₂₁ c) |in-ctx ap to) |in-ctx (λ u → ap (left ∘ left) (! (H₁₁ c)) ∙ u ∙ ap (left ∘ right) (H₃₁ c)))
            ∙ (ap-! (left ∘ left) (H₁₁ c) |in-ctx (λ u → u ∙ ap to (glue (left (f₂₁ c))) ∙ ap (left ∘ right) (H₃₁ c)))))

      =⟨ coh3 {f = λ u → ap (left ∘ left) (! (H₁₁ c)) ∙ u ∙ ap (left ∘ right) (H₃₁ c)}
              {p = ap-∘ left f∙₁ (glue c)}
              {ap (ap left) (F∙₁.glue-β c)}
              {ap-∙∙`∘`∘ left left right (! (H₁₁ c)) (glue (f₂₁ c)) (H₃₁ c)}
              {ap-∘ to i∙₀ (glue (f₂₁ c))}
              {I∙₀.glue-β (f₂₁ c) |in-ctx ap to}
              {To.glue-β (left (f₂₁ c))}
              {ap-∙∙`∘`∘ (to ∘ i∙₀) left right (! (H₁₁ c)) (glue (f₂₁ c)) (H₃₁ c)}
              {ap (ap (to ∘ i∙₀)) (F∙₁.glue-β c)}
              {ap-∘ (to ∘ i∙₀) f∙₁ (glue c)}
              (!-ap-∘ (to ∘ i∙₀) f∙₁ (glue c))
              {ap-!∙∙`∘`∘ left left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c)}
              {(! (To.glue-β (left (f₂₁ c)))) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (left ∘ right) (H₃₁ c))}
              {ap-! (left ∘ left) (H₁₁ c) |in-ctx (λ u → u ∙ ap to (glue (left (f₂₁ c))) ∙ ap (left ∘ right) (H₃₁ c))}
              (ap-!∙∙`∘`∘-coh left left right (H₁₁ c) (! (To.glue-β (left (f₂₁ c)))) (H₃₁ c)) ⟩

    end-lemma3 ∎  where

      coh2 : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {a b c d e o : B} (p : a == b) (q : b == c) (r : c == d) (s : d == e)
        {g h l m n : A} (y : o == f g) (x : g == h) (w : h == l) (v : l == m) (u : m == n) (t : f n == e)
        {u' : n == m} (γ : ! u == u') {w' : l == h} (δ : ! w == w') {x' : h == g} (α : ! x == x') {y' : f g == o} (β : ! y' == y)
        →
        (_ =⟨ p ⟩ _ =⟨ q ⟩ _ =⟨ r ⟩ _ ∎) ∙ s ∙ ! t ∙ ap f (_ =⟨ u' ⟩ _ =⟨ ! v ⟩ _ =⟨ w' ⟩ _ =⟨ x' ⟩ _ ∎) ∙ y'
        == p ∙ q ∙ r ∙ s ∙ ! ((y ∙ ap f x ∙ ap f w) ∙ (ap f v ∙ ap f u ∙ t))
      coh2 f idp idp idp idp .idp idp idp idp idp idp idp idp idp {y' = idp} idp = idp

      coh3 : ∀ {i j} {A : Type i} {B : Type j} {f : A → B} {a b c d e g o o' : B} {h k l m : A}
        {p : a == b} {q : b == c} {r : c == f m} {v : h == k} {w : k == l} {x : l == m}
        {s : d == f h} {t : e == d} {u : g == e} {u' : e == g} (α : ! u == u')
        {r' : c == o} {x' : o == o'} {y : f l == o'}
        (β : (r' ∙ x' ∙ ! y) == (r ∙' (! x |in-ctx f)))
        →
        p ∙ q ∙ r' ∙ x' ∙ ! ((u ∙ t) ∙ (s ∙ (v |in-ctx f) ∙ (w |in-ctx f) ∙ y))
        ==
        (_ =⟨ p ⟩ _ =⟨ q ⟩ _ =⟨ r ⟩ _ =⟨ ! (_ =⟨ v ⟩ _ =⟨ w ⟩ _ =⟨ x ⟩ _ ∎) |in-ctx f ⟩
         _ =⟨ ! s ⟩ _ =⟨ ! t ⟩ _ =⟨ u' ⟩ _ ∎)
      coh3 {p = idp} {idp} {._} {idp} {idp} {idp} {s} {idp} {idp} idp {idp} {idp} {y} idp = coh' s y  where

        coh' : ∀ {i} {B : Type i} {a b c : B} (s : a == b) (y : b == c)
          → ! (s ∙ y) == (_ =⟨ idp ⟩ _ =⟨ idp ⟩ _ =⟨ ! y ⟩ _ =⟨ idp ⟩ _ =⟨ ! s ⟩ _ ∎)
        coh' idp idp = idp

      lm =
        (ap-∘ to (i∙₀ ∘ f∙₁) (glue c)
         ∙ ap (ap to) (ap-∘ i∙₀ f∙₁ (glue c))
         ∙ ap (ap to) ((F∙₁.glue-β c) |in-ctx (λ u → ap i∙₀ u)))
        ∙ (ap (ap to) (ap-!∙∙`∘`∘ i∙₀ left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c))
           ∙ ap (ap to) ((I∙₀.glue-β (f₂₁ c)) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c)))
           ∙ ap-!'∙∙`∘`∘ to (left ∘ left) (right ∘ left) (H₁₁ c) (glue (left (f₂₁ c))) (H₃₁ c))

          =⟨ ap-∘-coh2 to i∙₀ f∙₁ (glue c) (F∙₁.glue-β c) |in-ctx (λ u → u ∙ (ap (ap to) (ap-!∙∙`∘`∘ i∙₀ left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c))
           ∙ ap (ap to) ((I∙₀.glue-β (f₂₁ c)) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c)))
           ∙ ap-!'∙∙`∘`∘ to (left ∘ left) (right ∘ left) (H₁₁ c) (glue (left (f₂₁ c))) (H₃₁ c))) ⟩

        (ap-∘ (to ∘ i∙₀) f∙₁ (glue c)
         ∙ ap (ap (to ∘ i∙₀)) (F∙₁.glue-β c)
         ∙ ap-∘ to i∙₀ (ap left (! (H₁₁ c)) ∙ glue (f₂₁ c) ∙ ap right (H₃₁ c)))
        ∙ (ap (ap to) (ap-!∙∙`∘`∘ i∙₀ left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c))
           ∙ ap (ap to) ((I∙₀.glue-β (f₂₁ c)) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c)))
           ∙ ap-!'∙∙`∘`∘ to (left ∘ left) (right ∘ left) (H₁₁ c) (glue (left (f₂₁ c))) (H₃₁ c))

          =⟨ assoc (ap-∘ (to ∘ i∙₀) f∙₁ (glue c))
                   (ap (ap (to ∘ i∙₀)) (F∙₁.glue-β c))
                   (ap-∘ to i∙₀ (ap left (! (H₁₁ c)) ∙ glue (f₂₁ c) ∙ ap right (H₃₁ c)))
                   (ap (ap to) (ap-!∙∙`∘`∘ i∙₀ left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c)))
                   (ap (ap to) ((I∙₀.glue-β (f₂₁ c)) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c))))
                   (ap-!'∙∙`∘`∘ to (left ∘ left) (right ∘ left) (H₁₁ c) (glue (left (f₂₁ c))) (H₃₁ c)) ⟩

        (ap-∘ (to ∘ i∙₀) f∙₁ (glue c)
         ∙ ap (ap (to ∘ i∙₀)) (F∙₁.glue-β c))
        ∙ (ap-∘ to i∙₀ (ap left (! (H₁₁ c)) ∙ glue (f₂₁ c) ∙ ap right (H₃₁ c))
           ∙ ap (ap to) (ap-!∙∙`∘`∘ i∙₀ left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c))
           ∙ ap (ap to) ((I∙₀.glue-β (f₂₁ c)) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c)))
           ∙ ap-!'∙∙`∘`∘ to (left ∘ left) (right ∘ left) (H₁₁ c) (glue (left (f₂₁ c))) (H₃₁ c))

          =⟨ ap-∘-ap-∙∙5`∘`∘-coh to i∙₀ left right (H₁₁ c) (I∙₀.glue-β (f₂₁ c)) (H₃₁ c) |in-ctx (λ u → (ap-∘ (to ∘ i∙₀) f∙₁ (glue c) ∙ ap (ap (to ∘ i∙₀)) (F∙₁.glue-β c)) ∙ u) ⟩

        (ap-∘ (to ∘ i∙₀) f∙₁ (glue c)
         ∙ ap (ap (to ∘ i∙₀)) (F∙₁.glue-β c))
        ∙ (ap-∙∙`∘`∘ (to ∘ i∙₀) left right (! (H₁₁ c)) (glue (f₂₁ c)) (H₃₁ c)
          ∙ (ap-∘ to i∙₀ (glue (f₂₁ c)) |in-ctx (λ u → ap (left ∘ left) (! (H₁₁ c)) ∙ u ∙ ap (left ∘ right) (H₃₁ c)))
          ∙ ((I∙₀.glue-β (f₂₁ c) |in-ctx ap to) |in-ctx (λ u → ap (left ∘ left) (! (H₁₁ c)) ∙ u ∙ ap (left ∘ right) (H₃₁ c)))
          ∙ (ap-! (left ∘ left) (H₁₁ c) |in-ctx (λ u → u ∙ ap to (glue (left (f₂₁ c))) ∙ ap (left ∘ right) (H₃₁ c)))) ∎ where

          assoc : ∀ {i} {A : Type i} {a b c d e f g : A} (p : a == b) (q : b == c) (r : c == d) (s : d == e) (t : e == f) (u : f == g)
            → (p ∙ q ∙ r) ∙ (s ∙ t ∙ u) == (p ∙ q) ∙ (r ∙ s ∙ t ∙ u)
          assoc idp idp idp idp idp idp = idp

  lemma2-2' =
    ap□ to (E∙₂Red.coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                            ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /)
              ∙□-i/ E∙₂Red.lhs-o c / E∙₂Red.rhs-o c /)
    ∙□-i/ ap-∘ to (i∙₄ ∘ f∙₃) (glue c) / ∘-ap to (i∙₀ ∘ f∙₁) (glue c) /

         =⟨ lemma2-3 |in-ctx (λ u → u ∙□-i/ ap-∘ to (i∙₄ ∘ f∙₃) (glue c) / ∘-ap to (i∙₀ ∘ f∙₁) (glue c) /) ⟩

    ↓-='-out (apd (glue {d = h-v-span}) (glue c))
    ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /
    ∙□-o/ ∘-ap to left (glue (f₁₂ c)) ∙ I₀∙.glue-β (f₁₂ c) / ! (∘-ap to right (glue (f₃₂ c)) ∙ I₄∙.glue-β (f₃₂ c)) /
    ∙□-i/ (To.glue-β (right (f₂₃ c))) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c)))
        / (! (To.glue-β (left (f₂₁ c)))) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (left ∘ right) (H₃₁ c)) /
    ∙□-i/ E∙₂Red.ap-ap-coh!-lhs-o c to / E∙₂Red.ap-ap-coh!-rhs-o c to /
    ∙□-i/ ap (ap to) (E∙₂Red.lhs-o c) / ap (ap to) (E∙₂Red.rhs-o c) /
    ∙□-i/ ap-∘ to (i∙₄ ∘ f∙₃) (glue c) / ∘-ap to (i∙₀ ∘ f∙₁) (glue c) /

         =⟨ assoc (↓-='-out (apd (glue {d = h-v-span}) (glue c))) (E₂∙Red.lhs-i c) ((To.glue-β (right (f₂₃ c))) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c)))) (E∙₂Red.ap-ap-coh!-lhs-o c to) (ap (ap to) (E∙₂Red.lhs-o c)) (ap-∘ to (i∙₄ ∘ f∙₃) (glue c)) _ _ _ _ _ (∘-ap to left (glue (f₁₂ c)) ∙ I₀∙.glue-β (f₁₂ c)) _ ⟩

    ↓-='-out (apd (glue {d = h-v-span}) (glue c))
    ∙□-o/ ∘-ap to left (glue (f₁₂ c)) ∙ I₀∙.glue-β (f₁₂ c) / ! (∘-ap to right (glue (f₃₂ c)) ∙ I₄∙.glue-β (f₃₂ c)) /
    ∙□-i/ ap-∘ to (i∙₄ ∘ f∙₃) (glue c)
          ∙ ap (ap to) (E∙₂Red.lhs-o c)
          ∙ E∙₂Red.ap-ap-coh!-lhs-o c to
          ∙ ((To.glue-β (right (f₂₃ c))) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c))))
          ∙ E₂∙Red.lhs-i c
        / E₂∙Red.rhs-i c
          ∙ ((! (To.glue-β (left (f₂₁ c)))) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (left ∘ right) (H₃₁ c)))
          ∙ E∙₂Red.ap-ap-coh!-rhs-o c to
          ∙ ap (ap to) (E∙₂Red.rhs-o c)
          ∙ ∘-ap to (i∙₀ ∘ f∙₁) (glue c) /

         =⟨ ∙□-i/-rewrite (↓-='-out (apd (glue {d = h-v-span}) (glue c))
    ∙□-o/ ∘-ap to left (glue (f₁₂ c)) ∙ I₀∙.glue-β (f₁₂ c) / ! (∘-ap to right (glue (f₃₂ c)) ∙ I₄∙.glue-β (f₃₂ c)) /) lemma2'-3 lemma2'-4 ⟩

    ↓-='-out (apd (glue {d = h-v-span}) (glue c))
    ∙□-o/ ∘-ap to left (glue (f₁₂ c)) ∙ I₀∙.glue-β (f₁₂ c) / ! (∘-ap to right (glue (f₃₂ c)) ∙ I₄∙.glue-β (f₃₂ c)) /
    ∙□-i/ ! end-lemma1 / end-lemma3 / ∎  where

      assoc : ∀ {i} {A : Type i} {a b b' c : A} {u u' : a == b} {v v1 v2 v3 v4 v5 : b == c}
         {w w1 w2 w3 w4 w5 : a == b'} {x x' : b' == c} (α : (u , v =□ w , x))
         (p1 : v1 == v) (p2 : v2 == v1) (p3 : v3 == v2) (p4 : v4 == v3) (p5 : v5 == v4)
         (q1 : w == w1) (q2 : w1 == w2) (q3 : w2 == w3) (q4 : w3 == w4) (q5 : w4 == w5)
         (r : u' == u) (s : x == x')
         → α ∙□-i/ p1 / q1 / ∙□-o/ r / s / ∙□-i/ p2 / q2 / ∙□-i/ p3 / q3 / ∙□-i/ p4 / q4 / ∙□-i/ p5 / q5 /
         == α ∙□-o/ r / s / ∙□-i/ p5 ∙ p4 ∙ p3 ∙ p2 ∙ p1 / q1 ∙ q2 ∙ q3 ∙ q4 ∙ q5 /
      assoc α idp idp idp idp idp idp idp idp idp idp idp idp = idp

  lemma2-2 =
    ap↓ (ap to) (↓-='-in (E∙₂Red.coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                                          ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /)
                            ∙□-i/ E∙₂Red.lhs-o c / E∙₂Red.rhs-o c /))

         =⟨ ap↓-↓-='-in-β _ _ to (E∙₂Red.coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                                                  ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /)
                                    ∙□-i/ E∙₂Red.lhs-o c / E∙₂Red.rhs-o c /) ⟩

    ↓-='-in ((ap□ to (E∙₂Red.coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                                      ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /)
                        ∙□-i/ E∙₂Red.lhs-o c / E∙₂Red.rhs-o c /))
             ∙□-i/ ap-∘ to (i∙₄ ∘ f∙₃) (glue c) / ∘-ap to (i∙₀ ∘ f∙₁) (glue c) /)

         =⟨ lemma2-2' |in-ctx ↓-='-in ⟩

    ↓-='-in (↓-='-out (apd (glue {d = h-v-span}) (glue c))
             ∙□-o/ ∘-ap to left (glue (f₁₂ c)) ∙ I₀∙.glue-β (f₁₂ c) / ! (∘-ap to right (glue (f₃₂ c)) ∙ I₄∙.glue-β (f₃₂ c)) /
             ∙□-i/ ! end-lemma1 / end-lemma3 /) ∎

  lemma2-1 =
    apd (ap to ∘ ap from ∘ glue) (glue c)

         =⟨ apd-∘' (ap to ∘ ap from) glue (glue c) ⟩

    ap↓ (ap to ∘ ap from) (apd (glue {d = h-v-span}) (glue c))

         =⟨ ap↓-∘ (ap to) (ap from) (apd glue (glue c)) ⟩

    ap↓ (ap to) (ap↓ (ap from) (apd glue (glue c)))

         =⟨ from-glue-glue-β c |in-ctx (ap↓ (ap to)) ⟩

    ap↓ (ap to) ((↓-='-in (E∙₂Red.coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                                           ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /)
                             ∙□-i/ E∙₂Red.lhs-o c / E∙₂Red.rhs-o c /))
                   ◃/ From.glue-β (left (f₁₂ c)) / ! (From.glue-β (right (f₃₂ c))) /)

         =⟨ ap↓-◃/ (ap to) _ (From.glue-β (left (f₁₂ c))) _ ⟩

    ap↓ (ap to) (↓-='-in (E∙₂Red.coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                                          ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /)
                            ∙□-i/ E∙₂Red.lhs-o c / E∙₂Red.rhs-o c /))
    ◃/ ap (ap to) (From.glue-β (left (f₁₂ c))) / ap (ap to) (! (From.glue-β (right (f₃₂ c)))) /

         =⟨ lemma2-2 |in-ctx (λ u → u ◃/ ap (ap to) (From.glue-β (left (f₁₂ c))) / ap (ap to) (! (From.glue-β (right (f₃₂ c)))) /) ⟩

    ↓-='-in (↓-='-out (apd (glue {d = h-v-span}) (glue c))
             ∙□-o/ ∘-ap to left (glue (f₁₂ c)) ∙ I₀∙.glue-β (f₁₂ c) / ! (∘-ap to right (glue (f₃₂ c)) ∙ I₄∙.glue-β (f₃₂ c)) /
             ∙□-i/ ! end-lemma1 / end-lemma3 /)
    ◃/ ap (ap to) (From.glue-β (left (f₁₂ c))) / ap (ap to) (! (From.glue-β (right (f₃₂ c)))) / ∎

  lemma2 =
    ↓-='-out (apd (ap to ∘ ap from ∘ glue) (glue c))

         =⟨ lemma2-1 |in-ctx ↓-='-out ⟩

    ↓-='-out (↓-='-in (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                       ∙□-o/ ∘-ap to left (glue (f₁₂ c)) ∙ I₀∙.glue-β (f₁₂ c)
                           / ! (∘-ap to right (glue (f₃₂ c)) ∙ I₄∙.glue-β (f₃₂ c)) /
                       ∙□-i/ ! end-lemma1
                           / end-lemma3 /)
              ◃/ ap (ap to) (From.glue-β (left (f₁₂ c))) / ap (ap to) (! (From.glue-β (right (f₃₂ c)))) /)

         =⟨ thing (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                       ∙□-o/ ∘-ap to left (glue (f₁₂ c)) ∙ I₀∙.glue-β (f₁₂ c)
                           / ! (∘-ap to right (glue (f₃₂ c)) ∙ I₄∙.glue-β (f₃₂ c)) /
                       ∙□-i/ ! end-lemma1
                           / end-lemma3 /) (ap (ap to) (From.glue-β (left (f₁₂ c)))) (ap (ap to) (! (From.glue-β (right (f₃₂ c))))) ⟩

    ↓-='-out (apd (glue {d = h-v-span}) (glue c))
    ∙□-o/ ∘-ap to left (glue (f₁₂ c)) ∙ I₀∙.glue-β (f₁₂ c)
        / ! (∘-ap to right (glue (f₃₂ c)) ∙ I₄∙.glue-β (f₃₂ c)) /
    ∙□-i/ ! end-lemma1
        / end-lemma3 /
    ∙□-o/ ap (ap to) (From.glue-β (left (f₁₂ c))) / ap (ap to) (! (From.glue-β (right (f₃₂ c)))) /

         =⟨ ch (↓-='-out (apd (glue {d = h-v-span}) (glue c))) (∘-ap to left (glue (f₁₂ c)))
               (ap-∘ to left (glue (f₁₂ c))) (!-∘-ap to left (glue (f₁₂ c))) (I₀∙.glue-β (f₁₂ c)) (∘-ap to right (glue (f₃₂ c)))
               (ap-∘ to right (glue (f₃₂ c))) (!-∘-ap to right (glue (f₃₂ c))) (I₄∙.glue-β (f₃₂ c)) (! end-lemma1) end-lemma3
               (ap (ap to) (From.glue-β (left (f₁₂ c)))) (! (From.glue-β (left (f₁₂ c))) |in-ctx ap to) (!-ap (ap to) (From.glue-β (left (f₁₂ c)))) (ap (ap to) (! (From.glue-β (right (f₃₂ c))))) ⟩

    ↓-='-out (apd (glue {d = h-v-span}) (glue c))
    ∙□-i/ ! end-lemma1
        / end-lemma3 /
    ∙□-o/ ! (to-from-g-l (f₁₂ c))
        / to-from-g-r (f₃₂ c) / ∎  where


      ch : ∀ {i} {A : Type i} {a b b' c : A} {p₁ p₂ p₃ p₄ : a == b} {q₁ q₂ : b == c} {r₁ r₂ : a == b'}
           {s₁ s₂ s₃ s₄ : b' == c} (α : (p₁ , q₁ =□ r₁ , s₁)) (β₁ : p₃ == p₂) (β₁-inv : p₂ == p₃)
           (eq : ! β₁ == β₁-inv) (β₂ : p₂ == p₁) (β'₁ : s₃ == s₂)
           (β'₁-inv : s₂ == s₃) (eq' : ! β'₁ == β'₁-inv) (β'₂ : s₂ == s₁)
           (γ : q₂ == q₁) (γ' : r₁ == r₂) (β₃ : p₄ == p₃) (β₃-inv : p₃ == p₄) (eq₃ : ! β₃ == β₃-inv) (β'₃ : s₃ == s₄)
           →
           α ∙□-o/ β₁ ∙ β₂ / ! (β'₁ ∙ β'₂) /
             ∙□-i/ γ / γ' /
             ∙□-o/ β₃ / β'₃ /
           ==
           α ∙□-i/ γ / γ' /
             ∙□-o/ ! (_ =⟨ ! β₂ ⟩ _ =⟨ β₁-inv ⟩ _ =⟨ β₃-inv ⟩ _ ∎) / (_ =⟨ ! β'₂ ⟩ _ =⟨ β'₁-inv ⟩ _ =⟨ β'₃ ⟩ _ ∎) /
      ch α idp .idp idp idp idp .idp idp idp idp idp idp .idp idp idp = idp

