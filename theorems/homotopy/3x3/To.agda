{-# OPTIONS --without-K --rewriting #-}

--open import HoTT
open import homotopy.3x3.PushoutPushout
open import homotopy.3x3.Transpose
open import homotopy.3x3.Common

module homotopy.3x3.To {i} (d : Span^2 {i}) where

open Span^2 d
open M d hiding (Pushout^2)
open M (transpose d) using () renaming (module F₁∙ to F∙₁; f₁∙ to f∙₁;
                                        module F₃∙ to F∙₃; f₃∙ to f∙₃;
                                        v-h-span to h-v-span)
open M using (Pushout^2)

module I₀∙ = PushoutRec {D = Pushout^2 (transpose d)}
                        (left ∘ left) (right ∘ left) (glue ∘ left)

i₀∙ : A₀∙ → Pushout^2 (transpose d)
i₀∙ = I₀∙.f

module I₄∙ = PushoutRec {D = Pushout^2 (transpose d)}
                        (left ∘ right) (right ∘ right) (glue ∘ right)

i₄∙ : A₄∙ → Pushout^2 (transpose d)
i₄∙ = I₄∙.f

module E₂∙Red (c : A₂₂) where

  -- lhs-o' : _
  -- lhs-o' =
  --     ap (i₄∙ ∘ f₃∙) (glue c)
  --        =⟨ ap-∘ i₄∙ f₃∙ (glue c) ⟩
  --     ap i₄∙ (ap f₃∙ (glue c))
  --          =⟨ F₃∙.glue-β c |in-ctx (ap i₄∙) ⟩
  --     ap i₄∙ (ap left (H₃₁ c) ∙ glue (f₃₂ c) ∙ ap right (H₃₃ c))
  --          =⟨ ap-∙∙`∘`∘ i₄∙ left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c) ⟩
  --     ap (left ∘ right) (H₃₁ c) ∙ ap i₄∙ (glue (f₃₂ c)) ∙ ap (right ∘ right) (H₃₃ c) ∎

  lhs-o : _
  lhs-o =
      ap (i₄∙ ∘ f₃∙) (glue c)
        =⟨ ap-∘ i₄∙ f₃∙ (glue c) ⟩
      ap i₄∙ (ap f₃∙ (glue c))
        =⟨ F₃∙.glue-β c |in-ctx (ap i₄∙) ⟩
      ap i₄∙ (ap left (H₃₁ c) ∙ glue (f₃₂ c) ∙ ap right (H₃₃ c))
        =⟨ ap-∙∙`∘`∘ i₄∙ left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c) ⟩
      ap (left ∘ right) (H₃₁ c) ∙ ap i₄∙ (glue (f₃₂ c)) ∙ ap (right ∘ right) (H₃₃ c)
        =⟨ I₄∙.glue-β (f₃₂ c) |in-ctx (λ u → ap (left ∘ right) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)) ⟩
      ap (left ∘ right) (H₃₁ c) ∙ glue (right (f₃₂ c)) ∙ ap (right ∘ right) (H₃₃ c) ∎

  rhs-o : _
  rhs-o =
      ap (left ∘ left) (H₁₁ c) ∙ glue (left (f₁₂ c)) ∙ ap (right ∘ left) (H₁₃ c)
           =⟨ ! (I₀∙.glue-β (f₁₂ c) |in-ctx (λ u → (ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c)))) ⟩
      ap (left ∘ left) (H₁₁ c) ∙ ap i₀∙ (glue (f₁₂ c)) ∙ ap (right ∘ left) (H₁₃ c)
           =⟨ ! (ap-∙∙`∘`∘ i₀∙ left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c)) ⟩
      ap i₀∙ (ap left (H₁₁ c) ∙ glue (f₁₂ c) ∙ ap right (H₁₃ c))
           =⟨ ! (F₁∙.glue-β c |in-ctx (λ u → ap i₀∙ u)) ⟩
      ap i₀∙ (ap f₁∙ (glue c))
           =⟨ ∘-ap i₀∙ f₁∙ (glue c) ⟩
      ap (i₀∙ ∘ f₁∙) (glue c) ∎

  T-lhs : Type _
  T-lhs = right (left (f₀₃ (f₁₂ c))) == right (right (f₄₃ (f₃₂ c))) :> Pushout^2 (transpose d)

  lhs-i : _ == _ :> T-lhs
  lhs-i =
      ap (right ∘ left) (H₁₃ c) ∙ ap right (glue (f₂₃ c)) ∙ ! (ap (right ∘ right) (H₃₃ c))
        =⟨ ! (ap-∙∙!`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c)) ⟩
      ap right (ap left (H₁₃ c) ∙ glue (f₂₃ c) ∙ ap right (! (H₃₃ c)))
        =⟨ ! (F∙₃.glue-β c) |in-ctx ap right ⟩
      ap right (ap f∙₃ (glue c))
        =⟨ ∘-ap right f∙₃ (glue c) ⟩
      ap (right ∘ f∙₃) (glue c) ∎

  T-rhs : Type _
  T-rhs = left (left (f₀₁ (f₁₂ c))) == left (right (f₄₁ (f₃₂ c))) :> Pushout^2 (transpose d)

  rhs-i : _ == _ :> T-rhs
  rhs-i = 
      ap (left ∘ f∙₁) (glue c)
        =⟨ ap-∘ left f∙₁ (glue c) ⟩
      ap left (ap f∙₁ (glue c))
        =⟨ F∙₁.glue-β c |in-ctx (ap left) ⟩
      ap left (ap left (! (H₁₁ c)) ∙ glue (f₂₁ c) ∙ ap right (H₃₁ c))
        =⟨ ap-!∙∙`∘`∘ left left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c) ⟩
      (! (ap (left ∘ left) (H₁₁ c)) ∙ ap left (glue (f₂₁ c)) ∙ ap (left ∘ right) (H₃₁ c)) ∎

  coh : (p : (_ , _ =□ _ , _)) → _
  coh = pp-coh {A = Pushout^2 (transpose d)}
               {p = glue (left (f₁₂ c))}
               {ap (right ∘ left) (H₁₃ c)}
               {ap right (glue (f₂₃ c))}
               {ap (right ∘ right) (H₃₃ c)}
               {ap (left ∘ left) (H₁₁ c)}
               {ap left (glue (f₂₁ c))}
               {ap (left ∘ right) (H₃₁ c)}
               {glue (right (f₃₂ c))}

  coh! : (p : _ , _ =□ _ , _) → _
  coh! = pp-coh! {A = Pushout^2 (transpose d)}
                 {u = ap left (glue (f₂₁ c))}
                 {ap (left ∘ right) (H₃₁ c)}
                 {glue (right (f₃₂ c))}
                 {ap (right ∘ right) (H₃₃ c)}
                 {ap (left ∘ left) (H₁₁ c)}
                 {glue (left (f₁₂ c))}
                 {ap (right ∘ left) (H₁₃ c)}
                 {ap right (glue (f₂₃ c))}

  module _ (f : Pushout^2 (transpose d) → Pushout^2 d) where

    ap-ap-coh : (p : _ , _ =□ _ , _) → _
    ap-ap-coh = pp-coh {p = ap f (glue (left (f₁₂ c)))}
                          {ap (f ∘ right ∘ left) (H₁₃ c)}
                          {ap f (ap right (glue (f₂₃ c)))}
                          {ap (f ∘ right ∘ right) (H₃₃ c)}
                          {ap (f ∘ left ∘ left) (H₁₁ c)}
                          {ap f (ap left (glue (f₂₁ c)))}
                          {ap (f ∘ left ∘ right) (H₃₁ c)}
                          {ap f (glue (right (f₃₂ c)))}

    ap-ap-coh! : (p : _ , _ =□ _ , _) → _
    ap-ap-coh! = pp-coh!
                          {u = ap f (ap left (glue (f₂₁ c)))}
                          {ap (f ∘ left ∘ right) (H₃₁ c)}
                          {ap f (glue (right (f₃₂ c)))}
                          {ap (f ∘ right ∘ right) (H₃₃ c)}
                          {ap (f ∘ left ∘ left) (H₁₁ c)}
                          {ap f (glue (left (f₁₂ c)))}
                          {ap (f ∘ right ∘ left) (H₁₃ c)}
                          {ap f (ap right (glue (f₂₃ c)))}

    ap-ap-coh-lhs-i : _
    ap-ap-coh-lhs-i = ! (ap-∙∙!'`∘`∘ f (right ∘ left) (right ∘ right) (H₁₃ c) (ap right (glue (f₂₃ c))) (H₃₃ c))

    ap-ap-coh-rhs-i : _
    ap-ap-coh-rhs-i = ap-!'∙∙`∘`∘ f (left ∘ left) (left ∘ right) (H₁₁ c) (ap left (glue (f₂₁ c))) (H₃₁ c)

    ap-ap-coh-lhs-o : _
    ap-ap-coh-lhs-o = ap-∙∙`∘`∘ f (left ∘ right) (right ∘ right) (H₃₁ c) (glue (right (f₃₂ c))) (H₃₃ c)

    ap-ap-coh-rhs-o : _
    ap-ap-coh-rhs-o = ! (ap-∙∙`∘`∘ f (left ∘ left) (right ∘ left) (H₁₁ c) (glue (left (f₁₂ c))) (H₁₃ c))

    ap-ap-coh-β : (α : _)
            → ap□ f (coh α) == ap-ap-coh (ap□ f α
                                          ∙□-i/ ap-ap-coh-lhs-i
                                              / ap-ap-coh-rhs-i /)
                               ∙□-i/ ap-ap-coh-lhs-o
                                   / ap-ap-coh-rhs-o /
    ap-ap-coh-β α = ap□-coh {g₁ = right ∘ left} {right ∘ right} {left ∘ left} {left ∘ right} f
                            {p = glue (left (f₁₂ c))} {H₁₃ c} {ap right (glue (f₂₃ c))} {H₃₃ c}
                            {H₁₁ c} {ap left (glue (f₂₁ c))} {H₃₁ c} {glue (right (f₃₂ c))}
                            α

open E₂∙Red

module E₂∙ = PushoutElim {d = span _ _ _ f₂₁ f₂₃} {P = λ c → i₀∙ (f₁∙ c) == i₄∙ (f₃∙ c)}
  (ap left ∘ glue) (ap right ∘ glue)
  (λ c → ↓-='-in' (coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                         ∙□-i/ lhs-i c / rhs-i c /)
                  ∙□-i/ lhs-o c / rhs-o c /))

e₂∙ : (c : A₂∙) → i₀∙ (f₁∙ c) == i₄∙ (f₃∙ c)
e₂∙ = E₂∙.f

module To = PushoutRec {d = v-h-span} {D = Pushout^2 (transpose d)}
                       i₀∙ i₄∙ e₂∙

to : Pushout^2 d → Pushout^2 (transpose d)
to = To.f

to-glue-glue-β : (c : A₂₂) → ap↓ (ap to) (apd glue (glue c))
                          == (↓-='-in' (coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                                              ∙□-i/ lhs-i c / rhs-i c /)
                                       ∙□-i/ lhs-o c / rhs-o c /))
                             ◃/ To.glue-β (left (f₂₁ c)) / ! (To.glue-β (right (f₂₃ c))) /
to-glue-glue-β c = ∘'-apd (ap to) glue (glue c)
                   ∙ coh1 {p = apd (ap to ∘ glue) (glue c)} {To.glue-β (right (f₂₃ c))}
                          {To.glue-β (left (f₂₁ c))} {apd e₂∙ (glue c)}
                          (↓-=-out (apd To.glue-β (glue c)))
                   ∙ (E₂∙.glue-β c |in-ctx (λ u → u ◃/ To.glue-β (left (f₂₁ c)) / ! (To.glue-β (right (f₂₃ c)))/))

{-
In ∞TT, this whole file would reduce to:

to : Pushout^2 d → Pushout^2 (transpose d)
to (left (left x)) = left (left x)
to (left (right x)) = right (left x)
ap to (ap left (glue x)) = glue (left x)
to (right (left x)) = left (right x)
to (right (right x)) = right (right x)
ap to (ap right (glue x)) = glue (right x)
ap to (glue (left x)) = ap left (glue x)
ap to (glue (right x)) = ap right (glue x)
ap (ap to) (ap glue (glue x)) = coh {t = ap left (ap left (H₁₁ c))} (ap glue (glue x))  where

    coh : ∀ {i} {A : Type i} {a b b' c c' d d' e : A}
      {p : a == b} {q : b == c} {r : c == d} {s : e == d}
      {t : b' == a} {u : b' == c'} {v : c' == d'} {w : d' == e}
      → (p ;; q ∙ r ∙ (! s)) == ((! t) ∙ u ∙ v) ;; w) → (u ;; v ∙ w ∙ s) == (t ∙ p ∙ q ;; r)
    coh {p = idp} {q} {idp} {idp} {idp} {idp} {idp} {idp} α = (! α) ∙ (∙-unit-r q)
-}
