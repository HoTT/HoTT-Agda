{-# OPTIONS --without-K --rewriting #-}

--open import HoTT
open import homotopy.3x3.PushoutPushout
open import homotopy.3x3.Transpose
import homotopy.3x3.To as To
import homotopy.3x3.From as From
open import homotopy.3x3.Common

module homotopy.3x3.FromTo3 {i} (d : Span^2 {i}) where

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

module M3 (c : A₂₂) where

  open M2 c

  lemma2-3 =
    ap□ from (E₂∙Red.coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                            ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /)
              ∙□-i/ E₂∙Red.lhs-o c / E₂∙Red.rhs-o c /)

         =⟨ ap□-∙□-i/ from _ (E₂∙Red.lhs-o c) (E₂∙Red.rhs-o c) ⟩

    ap□ from (E₂∙Red.coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                            ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /))
    ∙□-i/ ap (ap from) (E₂∙Red.lhs-o c) / ap (ap from) (E₂∙Red.rhs-o c) /

         =⟨ lemma2-4 |in-ctx (λ u → u ∙□-i/ ap (ap from) (E₂∙Red.lhs-o c) / ap (ap from) (E₂∙Red.rhs-o c) /) ⟩

    ↓-='-out (apd (glue {d = v-h-span}) (glue c))
    ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /
    ∙□-o/ ∘-ap from left (glue (f₂₁ c)) ∙ I∙₀.glue-β (f₂₁ c) / ! (∘-ap from right (glue (f₂₃ c)) ∙ I∙₄.glue-β (f₂₃ c)) /
    ∙□-i/ (From.glue-β (right (f₃₂ c))) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c))
        / (! (From.glue-β (left (f₁₂ c)))) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (left ∘ right) (H₁₃ c)) /
    ∙□-i/ E₂∙Red.ap-ap-coh-lhs-o c from / E₂∙Red.ap-ap-coh-rhs-o c from /
    ∙□-i/ ap (ap from) (E₂∙Red.lhs-o c) / ap (ap from) (E₂∙Red.rhs-o c) / ∎


  lemma2'-3 =
    ap-∘ from (i₄∙ ∘ f₃∙) (glue c)
    ∙ ap (ap from) (E₂∙Red.lhs-o c)
    ∙ E₂∙Red.ap-ap-coh-lhs-o c from
    ∙ ((From.glue-β (right (f₃₂ c))) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
    ∙ E∙₂Red.lhs-i c

      =⟨ coh2 (ap from)
              (ap-∘ from (i₄∙ ∘ f₃∙) (glue c))
              (ap-∘ i₄∙ f₃∙ (glue c))
              _
              _
              _
              (ap-∙∙`∘`∘ from (left ∘ right) (right ∘ right) (H₃₁ c) (glue (right (f₃₂ c))) (H₃₃ c))
              ((From.glue-β (right (f₃₂ c))) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
              (! (ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)))
              _
              _ ⟩

    (ap-∘ from (i₄∙ ∘ f₃∙) (glue c)
     ∙ ap (ap from) (ap-∘ i₄∙ f₃∙ (glue c))
     ∙ ap (ap from) (F₃∙.glue-β c |in-ctx (ap i₄∙)))

-- ap from (ap i₄∙ (ap left (H₃₁ c) ∙ glue (f₃₂ c) ∙ ap right (H₃₃ c)))

    ∙ (ap (ap from) (ap-∙∙`∘`∘ i₄∙ left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c))
       ∙ ap (ap from) (I₄∙.glue-β (f₃₂ c) |in-ctx (λ u → ap (left ∘ right) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
       ∙ ap-∙∙`∘`∘ from (left ∘ right) (right ∘ right) (H₃₁ c) (glue (right (f₃₂ c))) (H₃₃ c))

-- ap (right ∘ left) (H₃₁ c) ∙ ap from (glue (right (f₃₂ c))) ∙ ap (right ∘ right) (H₃₃ c)

    ∙ (((From.glue-β (right (f₃₂ c))) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
       ∙ ! (ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c))
       ∙ ! (ap (ap right) (F₃∙.glue-β c))
       ∙ ∘-ap right f₃∙ (glue c))

         =⟨ ap-∘-ap-∙∙`∘`∘-coh from i₄∙ left right (H₃₁ c) (I₄∙.glue-β (f₃₂ c)) (H₃₃ c)
            |in-ctx (λ u →
              (ap-∘ from (i₄∙ ∘ f₃∙) (glue c)
               ∙ ap (ap from) (ap-∘ i₄∙ f₃∙ (glue c))
               ∙ ap (ap from) (F₃∙.glue-β c |in-ctx (ap i₄∙)))
              ∙ u
              ∙ (((From.glue-β (right (f₃₂ c))) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
                 ∙ ! (ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c))
                 ∙ ! (ap (ap right) (F₃∙.glue-β c))
                 ∙ ∘-ap right f₃∙ (glue c))) ⟩


    (ap-∘ from (i₄∙ ∘ f₃∙) (glue c)
     ∙ ap (ap from) (ap-∘ i₄∙ f₃∙ (glue c))
     ∙ ap (ap from) (F₃∙.glue-β c |in-ctx (ap i₄∙)))

-- ap from (ap i₄∙ (ap left (H₃₁ c) ∙ glue (f₃₂ c) ∙ ap right (H₃₃ c)))

    ∙ (∘-ap from i₄∙ (ap left (H₃₁ c) ∙ glue (f₃₂ c) ∙ ap right (H₃₃ c))
       ∙ ap-∙∙`∘`∘ (from ∘ i₄∙) left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)
       ∙ (ap-∘ from i₄∙ (glue (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
       ∙ (ap (ap from) (I₄∙.glue-β (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c))))

-- ap (right ∘ left) (H₃₁ c) ∙ ap from (glue (right (f₃₂ c))) ∙ ap (right ∘ right) (H₃₃ c)

    ∙ (((From.glue-β (right (f₃₂ c))) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
       ∙ (! (ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)))
       ∙ ! (ap (ap right) (F₃∙.glue-β c))
       ∙ ∘-ap right f₃∙ (glue c))

         =⟨ coh3 (ap-∘ from (i₄∙ ∘ f₃∙) (glue c))
                 (ap (ap from) (ap-∘ i₄∙ f₃∙ (glue c)))
                 (ap (ap from) (F₃∙.glue-β c |in-ctx (ap i₄∙)))
                 (∘-ap from i₄∙ (ap left (H₃₁ c) ∙ glue (f₃₂ c) ∙ ap right (H₃₃ c)))
                 _
                 _ ⟩

    (ap-∘ from (i₄∙ ∘ f₃∙) (glue c)
     ∙ ap (ap from) (ap-∘ i₄∙ f₃∙ (glue c))
     ∙ ap (ap from) (F₃∙.glue-β c |in-ctx (ap i₄∙))
     ∙ ∘-ap from i₄∙ (ap left (H₃₁ c) ∙ glue (f₃₂ c) ∙ ap right (H₃₃ c)))
    ∙ (ap-∙∙`∘`∘ (from ∘ i₄∙) left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)
       ∙ (ap-∘ from i₄∙ (glue (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
       ∙ (ap (ap from) (I₄∙.glue-β (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c))))
    ∙ ((From.glue-β (right (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
       ∙ ! (ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c))
       ∙ ! (ap (ap right) (F₃∙.glue-β c))
       ∙ ∘-ap right f₃∙ (glue c))

         =⟨ ap-∘-coh from i₄∙ f₃∙ (glue c) (F₃∙.glue-β c)
           |in-ctx (λ u → u ∙ (ap-∙∙`∘`∘ (from ∘ i₄∙) left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)
                               ∙ (ap-∘ from i₄∙ (glue (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
                               ∙ (ap (ap from) (I₄∙.glue-β (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c))))
                            ∙ ((From.glue-β (right (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
                               ∙ ! (ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c))
                               ∙ ! (ap (ap right) (F₃∙.glue-β c))
                               ∙ ∘-ap right f₃∙ (glue c))) ⟩

    (ap-∘ (from ∘ i₄∙) f₃∙ (glue c)
     ∙ (ap (ap (from ∘ i₄∙)) (F₃∙.glue-β c)))
    ∙ (ap-∙∙`∘`∘ (from ∘ i₄∙) left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)
       ∙ (ap-∘ from i₄∙ (glue (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
       ∙ (ap (ap from) (I₄∙.glue-β (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c))))
    ∙ ((From.glue-β (right (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
       ∙ ! (ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c))
       ∙ ! (ap (ap right) (F₃∙.glue-β c))
       ∙ ∘-ap right f₃∙ (glue c))

      =⟨ !-ap-∘-inv right f₃∙ (glue c)
          |in-ctx (λ u → (ap-∘ (from ∘ i₄∙) f₃∙ (glue c)
     ∙ (ap (ap (from ∘ i₄∙)) (F₃∙.glue-β c)))
    ∙ (ap-∙∙`∘`∘ (from ∘ i₄∙) left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)
       ∙ (ap-∘ from i₄∙ (glue (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
       ∙ (ap (ap from) (I₄∙.glue-β (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c))))
    ∙ ((From.glue-β (right (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
       ∙ ! (ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c))
       ∙ ! (ap (ap right) (F₃∙.glue-β c))
       ∙ u)) ⟩

    (ap-∘ (from ∘ i₄∙) f₃∙ (glue c)
     ∙ (ap (ap (from ∘ i₄∙)) (F₃∙.glue-β c)))
    ∙ (ap-∙∙`∘`∘ (from ∘ i₄∙) left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)
       ∙ (ap-∘ from i₄∙ (glue (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
       ∙ (ap (ap from) (I₄∙.glue-β (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c))))
    ∙ ((From.glue-β (right (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
       ∙ ! (ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c))
       ∙ ! (ap (ap right) (F₃∙.glue-β c))
       ∙ ! (ap-∘ right f₃∙ (glue c)))

      =⟨ !-∘-ap-inv (from ∘ i₄∙) f₃∙ (glue c)
         |in-ctx (λ u → (u
     ∙ (ap (ap (from ∘ i₄∙)) (F₃∙.glue-β c)))
    ∙ (ap-∙∙`∘`∘ (from ∘ i₄∙) left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)
       ∙ (ap-∘ from i₄∙ (glue (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
       ∙ (ap (ap from) (I₄∙.glue-β (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c))))
    ∙ ((From.glue-β (right (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
       ∙ ! (ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c))
       ∙ ! (ap (ap right) (F₃∙.glue-β c))
       ∙ ! (ap-∘ right f₃∙ (glue c)))) ⟩

    (! (∘-ap (from ∘ i₄∙) f₃∙ (glue c))
     ∙ (ap (ap (from ∘ i₄∙)) (F₃∙.glue-β c)))
    ∙ (ap-∙∙`∘`∘ (from ∘ i₄∙) left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)
       ∙ (ap-∘ from i₄∙ (glue (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
       ∙ (ap (ap from) (I₄∙.glue-β (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c))))
    ∙ ((From.glue-β (right (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
       ∙ ! (ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c))
       ∙ ! (ap (ap right) (F₃∙.glue-β c))
       ∙ ! (ap-∘ right f₃∙ (glue c)))

      =⟨ coh4 (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c))
               (∘-ap (from ∘ i₄∙) f₃∙ (glue c)) _ _ _ _ _ _ _ _ ⟩

    ! end-lemma1 ∎  where

      coh2 : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {a b c d e : A} {g h k l m n : B}
        (p : g == f a) (q : a == b) (r : b == c) (s : c == d) (t : d == e) (u : f e == h) (v : h == k)
        (w : k == l) (x : l == m) (y : m == n)
        → p ∙ ap f (_ =⟨ q ⟩ _ =⟨ r ⟩ _ =⟨ s ⟩ _ =⟨ t ⟩ _ ∎) ∙ u ∙ v ∙ (_ =⟨ w ⟩ _ =⟨ x ⟩ _ =⟨ y ⟩ _ ∎)
          == (p ∙ ap f q ∙ ap f r) ∙ (ap f s ∙ ap f t ∙ u) ∙ (v ∙ w ∙ x ∙ y)
      coh2 f p idp idp idp idp idp idp idp idp idp = ! (∙-unit-r (p ∙ idp))

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


  lemma2'-4 =
    E∙₂Red.rhs-i c
    ∙ ((! (From.glue-β (left (f₁₂ c)))) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (left ∘ right) (H₁₃ c)))
    ∙ E₂∙Red.ap-ap-coh-rhs-o c from
    ∙ ap (ap from) (E₂∙Red.rhs-o c)
    ∙ ∘-ap from (i₀∙ ∘ f₁∙) (glue c)

      =⟨ coh2 (ap from)
           (ap-∘ left f₁∙ (glue c))
           (F₁∙.glue-β c |in-ctx (ap left))
           (ap-∙∙`∘`∘ left left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c))
           (! (From.glue-β (left (f₁₂ c))) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (left ∘ right) (H₁₃ c)))
           (ap-∘ from (i₀∙ ∘ f₁∙) (glue c))
           (ap-∘ i₀∙ f₁∙ (glue c))
           ((F₁∙.glue-β c) |in-ctx (λ u → ap i₀∙ u))
           (ap-∙∙`∘`∘ i₀∙ left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c))
           ((I₀∙.glue-β (f₁₂ c)) |in-ctx (λ u → (ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c))))
           (ap-∙∙`∘`∘ from (left ∘ left) (right ∘ left) (H₁₁ c) (glue (left (f₁₂ c))) (H₁₃ c))
           (!-ap-∘ i₀∙ f₁∙ (glue c))
           (!-∘-ap from (i₀∙ ∘ f₁∙) (glue c)) ⟩

    ap-∘ left f₁∙ (glue c)
    ∙ (F₁∙.glue-β c |in-ctx (ap left))
    ∙ (ap-∙∙`∘`∘ left left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c))
    ∙ (! (From.glue-β (left (f₁₂ c))) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (left ∘ right) (H₁₃ c)))
    ∙ ! ((ap-∘ from (i₀∙ ∘ f₁∙) (glue c)
          ∙ ap (ap from) (ap-∘ i₀∙ f₁∙ (glue c))
          ∙ ap (ap from) ((F₁∙.glue-β c) |in-ctx (λ u → ap i₀∙ u)))
         ∙ (ap (ap from) (ap-∙∙`∘`∘ i₀∙ left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c))
            ∙ ap (ap from) ((I₀∙.glue-β (f₁₂ c)) |in-ctx (λ u → (ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c))))
            ∙ ap-∙∙`∘`∘ from (left ∘ left) (right ∘ left) (H₁₁ c) (glue (left (f₁₂ c))) (H₁₃ c)))

      =⟨ lm |in-ctx (λ u →
    ap-∘ left f₁∙ (glue c)
    ∙ ap (ap left) (F₁∙.glue-β c)
    ∙ ap-∙∙`∘`∘ left left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c)
    ∙ (! (From.glue-β (left (f₁₂ c))) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (left ∘ right) (H₁₃ c)))
    ∙ ! u) ⟩

    ap-∘ left f₁∙ (glue c)
    ∙ ap (ap left) (F₁∙.glue-β c)
    ∙ ap-∙∙`∘`∘ left left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c)
    ∙ (! (From.glue-β (left (f₁₂ c))) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (left ∘ right) (H₁₃ c)))
    ∙ ! ((ap-∘ (from ∘ i₀∙) f₁∙ (glue c)
          ∙ ap (ap (from ∘ i₀∙)) (F₁∙.glue-β c))
         ∙ (ap-∙∙`∘`∘ (from ∘ i₀∙) left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c)
            ∙ (ap-∘ from i₀∙ (glue (f₁₂ c)) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (left ∘ right) (H₁₃ c)))
            ∙ ((I₀∙.glue-β (f₁₂ c) |in-ctx ap from) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (left ∘ right) (H₁₃ c)))))

      =⟨ coh3 {f = λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (left ∘ right) (H₁₃ c)}
              {p = ap-∘ left f₁∙ (glue c)}
              {ap (ap left) (F₁∙.glue-β c)}
              {ap-∙∙`∘`∘ left left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c)}
              {ap-∘ from i₀∙ (glue (f₁₂ c))}
              {I₀∙.glue-β (f₁₂ c) |in-ctx ap from}
              {From.glue-β (left (f₁₂ c))}
              {ap-∙∙`∘`∘ (from ∘ i₀∙) left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c)}
              {ap (ap (from ∘ i₀∙)) (F₁∙.glue-β c)}
              {ap-∘ (from ∘ i₀∙) f₁∙ (glue c)}
              (!-ap-∘ (from ∘ i₀∙) f₁∙ (glue c)) ⟩

    end-lemma3 ∎  where

      coh2 : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {a b c d e o : B} (p : a == b) (q : b == c) (r : c == d) (s : d == e)
        {g h l m n : A} (y : o == f g) (x : g == h) (w : h == l) (v : l == m) (u : m == n) (t : f n == e)
        {x' : h == g} (α : ! x == x') {y' : f g == o} (β : ! y' == y)
        →
        (_ =⟨ p ⟩ _ =⟨ q ⟩ _ =⟨ r ⟩ _ ∎) ∙ s ∙ ! t ∙ ap f (_ =⟨ ! u ⟩ _ =⟨ ! v ⟩ _ =⟨ ! w ⟩ _ =⟨ x' ⟩ _ ∎) ∙ y'
        == p ∙ q ∙ r ∙ s ∙ ! ((y ∙ ap f x ∙ ap f w) ∙ (ap f v ∙ ap f u ∙ t))
      coh2 f idp idp idp idp .idp idp idp idp idp idp idp {y' = idp} idp = idp

      coh3 : ∀ {i j} {A : Type i} {B : Type j} {f : A → B} {a b c d e g : B} {h k l m : A}
        {p : a == b} {q : b == c} {r : c == f m} {v : h == k} {w : k == l} {x : l == m}
        {s : d == f h} {t : e == d} {u : g == e} {u' : e == g} (α : ! u == u')
        →
        p ∙ q ∙ r ∙ (! x |in-ctx f) ∙ ! ((u ∙ t) ∙ (s ∙ (v |in-ctx f) ∙ (w |in-ctx f)))
        ==
        (_ =⟨ p ⟩ _ =⟨ q ⟩ _ =⟨ r ⟩ _ =⟨ ! (_ =⟨ v ⟩ _ =⟨ w ⟩ _ =⟨ x ⟩ _ ∎) |in-ctx f ⟩
         _ =⟨ ! s ⟩ _ =⟨ ! t ⟩ _ =⟨ u' ⟩ _ ∎)
      coh3 {p = idp} {idp} {r} {idp} {idp} {idp} {s} {idp} {idp} idp = coh' r s  where

        coh' : ∀ {i} {B : Type i} {a b c : B} (r : a == b) (s : c == b)
          → r ∙ ! (s ∙ idp) == (_ =⟨ idp ⟩ _ =⟨ idp ⟩ _ =⟨ r ⟩ _ =⟨ idp ⟩ _ =⟨ ! s ⟩ _ ∎)
        coh' idp idp = idp

      lm =
        (ap-∘ from (i₀∙ ∘ f₁∙) (glue c)
         ∙ ap (ap from) (ap-∘ i₀∙ f₁∙ (glue c))
         ∙ ap (ap from) ((F₁∙.glue-β c) |in-ctx (λ u → ap i₀∙ u)))
        ∙ (ap (ap from) (ap-∙∙`∘`∘ i₀∙ left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c))
           ∙ ap (ap from) ((I₀∙.glue-β (f₁₂ c)) |in-ctx (λ u → (ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c))))
           ∙ ap-∙∙`∘`∘ from (left ∘ left) (right ∘ left) (H₁₁ c) (glue (left (f₁₂ c))) (H₁₃ c))

          =⟨ ap-∘-coh2 from i₀∙ f₁∙ (glue c) (F₁∙.glue-β c) |in-ctx (λ u → u ∙ (ap (ap from) (ap-∙∙`∘`∘ i₀∙ left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c))
           ∙ ap (ap from) ((I₀∙.glue-β (f₁₂ c)) |in-ctx (λ u → (ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c))))
           ∙ ap-∙∙`∘`∘ from (left ∘ left) (right ∘ left) (H₁₁ c) (glue (left (f₁₂ c))) (H₁₃ c))) ⟩

        (ap-∘ (from ∘ i₀∙) f₁∙ (glue c)
         ∙ ap (ap (from ∘ i₀∙)) (F₁∙.glue-β c)
         ∙ ap-∘ from i₀∙ (ap left (H₁₁ c) ∙ glue (f₁₂ c) ∙ ap right (H₁₃ c)))
        ∙ (ap (ap from) (ap-∙∙`∘`∘ i₀∙ left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c))
           ∙ ap (ap from) ((I₀∙.glue-β (f₁₂ c)) |in-ctx (λ u → (ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c))))
           ∙ ap-∙∙`∘`∘ from (left ∘ left) (right ∘ left) (H₁₁ c) (glue (left (f₁₂ c))) (H₁₃ c))

          =⟨ assoc (ap-∘ (from ∘ i₀∙) f₁∙ (glue c))
                   (ap (ap (from ∘ i₀∙)) (F₁∙.glue-β c))
                   (ap-∘ from i₀∙ (ap left (H₁₁ c) ∙ glue (f₁₂ c) ∙ ap right (H₁₃ c)))
                   (ap (ap from) (ap-∙∙`∘`∘ i₀∙ left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c)))
                   (ap (ap from) ((I₀∙.glue-β (f₁₂ c)) |in-ctx (λ u → (ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c)))))
                   (ap-∙∙`∘`∘ from (left ∘ left) (right ∘ left) (H₁₁ c) (glue (left (f₁₂ c))) (H₁₃ c)) ⟩

        (ap-∘ (from ∘ i₀∙) f₁∙ (glue c)
         ∙ ap (ap (from ∘ i₀∙)) (F₁∙.glue-β c))
        ∙ (ap-∘ from i₀∙ (ap left (H₁₁ c) ∙ glue (f₁₂ c) ∙ ap right (H₁₃ c))
           ∙ ap (ap from) (ap-∙∙`∘`∘ i₀∙ left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c))
           ∙ ap (ap from) ((I₀∙.glue-β (f₁₂ c)) |in-ctx (λ u → (ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c))))
           ∙ ap-∙∙`∘`∘ from (left ∘ left) (right ∘ left) (H₁₁ c) (glue (left (f₁₂ c))) (H₁₃ c))

          =⟨ ap-∘-ap-∙∙4`∘`∘-coh from i₀∙ left right (H₁₁ c) (I₀∙.glue-β (f₁₂ c)) (H₁₃ c) |in-ctx (λ u → (ap-∘ (from ∘ i₀∙) f₁∙ (glue c) ∙ ap (ap (from ∘ i₀∙)) (F₁∙.glue-β c)) ∙ u) ⟩

        (ap-∘ (from ∘ i₀∙) f₁∙ (glue c)
         ∙ ap (ap (from ∘ i₀∙)) (F₁∙.glue-β c))
        ∙ (ap-∙∙`∘`∘ (from ∘ i₀∙) left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c)
           ∙ (ap-∘ from i₀∙ (glue (f₁₂ c)) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (left ∘ right) (H₁₃ c)))
           ∙ ((I₀∙.glue-β (f₁₂ c) |in-ctx ap from) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (left ∘ right) (H₁₃ c)))) ∎  where

          assoc : ∀ {i} {A : Type i} {a b c d e f g : A} (p : a == b) (q : b == c) (r : c == d) (s : d == e) (t : e == f) (u : f == g)
            → (p ∙ q ∙ r) ∙ (s ∙ t ∙ u) == (p ∙ q) ∙ (r ∙ s ∙ t ∙ u)
          assoc idp idp idp idp idp idp = idp

  lemma2-2' =
    ap□ from (E₂∙Red.coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                            ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /)
              ∙□-i/ E₂∙Red.lhs-o c / E₂∙Red.rhs-o c /)
    ∙□-i/ ap-∘ from (i₄∙ ∘ f₃∙) (glue c) / ∘-ap from (i₀∙ ∘ f₁∙) (glue c) /

         =⟨ lemma2-3 |in-ctx (λ u → u ∙□-i/ ap-∘ from (i₄∙ ∘ f₃∙) (glue c) / ∘-ap from (i₀∙ ∘ f₁∙) (glue c) /) ⟩

    ↓-='-out (apd (glue {d = v-h-span}) (glue c))
    ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /
    ∙□-o/ ∘-ap from left (glue (f₂₁ c)) ∙ I∙₀.glue-β (f₂₁ c) / ! (∘-ap from right (glue (f₂₃ c)) ∙ I∙₄.glue-β (f₂₃ c)) /
    ∙□-i/ (From.glue-β (right (f₃₂ c))) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c))
        / (! (From.glue-β (left (f₁₂ c)))) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (left ∘ right) (H₁₃ c)) /
    ∙□-i/ E₂∙Red.ap-ap-coh-lhs-o c from / E₂∙Red.ap-ap-coh-rhs-o c from /
    ∙□-i/ ap (ap from) (E₂∙Red.lhs-o c) / ap (ap from) (E₂∙Red.rhs-o c) /
    ∙□-i/ ap-∘ from (i₄∙ ∘ f₃∙) (glue c) / ∘-ap from (i₀∙ ∘ f₁∙) (glue c) /

         =⟨ assoc (↓-='-out (apd (glue {d = v-h-span}) (glue c))) (E∙₂Red.lhs-i c)
                  ((From.glue-β (right (f₃₂ c))) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
                  (E₂∙Red.ap-ap-coh-lhs-o c from) (ap (ap from) (E₂∙Red.lhs-o c)) (ap-∘ from (i₄∙ ∘ f₃∙) (glue c)) _ _ _ _ _
                  (∘-ap from left (glue (f₂₁ c)) ∙ I∙₀.glue-β (f₂₁ c)) _ ⟩

    ↓-='-out (apd (glue {d = v-h-span}) (glue c))
    ∙□-o/ ∘-ap from left (glue (f₂₁ c)) ∙ I∙₀.glue-β (f₂₁ c) / ! (∘-ap from right (glue (f₂₃ c)) ∙ I∙₄.glue-β (f₂₃ c)) /
    ∙□-i/ ap-∘ from (i₄∙ ∘ f₃∙) (glue c)
          ∙ ap (ap from) (E₂∙Red.lhs-o c)
          ∙ E₂∙Red.ap-ap-coh-lhs-o c from
          ∙ ((From.glue-β (right (f₃₂ c))) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
          ∙ E∙₂Red.lhs-i c
        / E∙₂Red.rhs-i c
          ∙ ((! (From.glue-β (left (f₁₂ c)))) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (left ∘ right) (H₁₃ c)))
          ∙ E₂∙Red.ap-ap-coh-rhs-o c from
          ∙ ap (ap from) (E₂∙Red.rhs-o c)
          ∙ ∘-ap from (i₀∙ ∘ f₁∙) (glue c) /

         =⟨ ∙□-i/-rewrite (↓-='-out (apd (glue {d = v-h-span}) (glue c))
    ∙□-o/ ∘-ap from left (glue (f₂₁ c)) ∙ I∙₀.glue-β (f₂₁ c) / ! (∘-ap from right (glue (f₂₃ c)) ∙ I∙₄.glue-β (f₂₃ c)) /) lemma2'-3 lemma2'-4 ⟩

    ↓-='-out (apd (glue {d = v-h-span}) (glue c))
    ∙□-o/ ∘-ap from left (glue (f₂₁ c)) ∙ I∙₀.glue-β (f₂₁ c) / ! (∘-ap from right (glue (f₂₃ c)) ∙ I∙₄.glue-β (f₂₃ c)) /
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
    ap↓ (ap from) (↓-='-in' (E₂∙Red.coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                                          ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /)
                            ∙□-i/ E₂∙Red.lhs-o c / E₂∙Red.rhs-o c /))

         =⟨ ap↓-↓-='-in-β _ _ from (E₂∙Red.coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                                                  ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /)
                                    ∙□-i/ E₂∙Red.lhs-o c / E₂∙Red.rhs-o c /) ⟩

    ↓-='-in' ((ap□ from (E₂∙Red.coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                                      ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /)
                        ∙□-i/ E₂∙Red.lhs-o c / E₂∙Red.rhs-o c /))
             ∙□-i/ ap-∘ from (i₄∙ ∘ f₃∙) (glue c) / ∘-ap from (i₀∙ ∘ f₁∙) (glue c) /)

         =⟨ lemma2-2' |in-ctx ↓-='-in' ⟩

    ↓-='-in' (↓-='-out (apd (glue {d = v-h-span}) (glue c))
             ∙□-o/ ∘-ap from left (glue (f₂₁ c)) ∙ I∙₀.glue-β (f₂₁ c) / ! (∘-ap from right (glue (f₂₃ c)) ∙ I∙₄.glue-β (f₂₃ c)) /
             ∙□-i/ ! end-lemma1 / end-lemma3 /) ∎

  lemma2-1 =
    apd (ap from ∘ ap to ∘ glue) (glue c)

         =⟨ apd-∘' (ap from ∘ ap to) glue (glue c) ⟩

    ap↓ (ap from ∘ ap to) (apd (glue {d = v-h-span}) (glue c))

         =⟨ ap↓-∘ (ap from) (ap to) (apd glue (glue c)) ⟩

    ap↓ (ap from) (ap↓ (ap to) (apd glue (glue c)))

         =⟨ to-glue-glue-β c |in-ctx (ap↓ (ap from)) ⟩

    ap↓ (ap from) ((↓-='-in' (E₂∙Red.coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                                           ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /)
                             ∙□-i/ E₂∙Red.lhs-o c / E₂∙Red.rhs-o c /))
                   ◃/ To.glue-β (left (f₂₁ c)) / ! (To.glue-β (right (f₂₃ c))) /)

         =⟨ ap↓-◃/ (ap from) _ (To.glue-β (left (f₂₁ c))) _ ⟩

    ap↓ (ap from) (↓-='-in' (E₂∙Red.coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                                          ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /)
                            ∙□-i/ E₂∙Red.lhs-o c / E₂∙Red.rhs-o c /))
    ◃/ ap (ap from) (To.glue-β (left (f₂₁ c))) / ap (ap from) (! (To.glue-β (right (f₂₃ c)))) /

         =⟨ lemma2-2 |in-ctx (λ u → u ◃/ ap (ap from) (To.glue-β (left (f₂₁ c))) / ap (ap from) (! (To.glue-β (right (f₂₃ c)))) /) ⟩

    ↓-='-in' (↓-='-out (apd (glue {d = v-h-span}) (glue c))
             ∙□-o/ ∘-ap from left (glue (f₂₁ c)) ∙ I∙₀.glue-β (f₂₁ c) / ! (∘-ap from right (glue (f₂₃ c)) ∙ I∙₄.glue-β (f₂₃ c)) /
             ∙□-i/ ! end-lemma1 / end-lemma3 /)
    ◃/ ap (ap from) (To.glue-β (left (f₂₁ c))) / ap (ap from) (! (To.glue-β (right (f₂₃ c)))) / ∎

  lemma2 =
    ↓-='-out (apd (ap from ∘ ap to ∘ glue) (glue c))

         =⟨ lemma2-1 |in-ctx ↓-='-out ⟩

    ↓-='-out (↓-='-in' (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                       ∙□-o/ ∘-ap from left (glue (f₂₁ c)) ∙ I∙₀.glue-β (f₂₁ c)
                           / ! (∘-ap from right (glue (f₂₃ c)) ∙ I∙₄.glue-β (f₂₃ c)) /
                       ∙□-i/ ! end-lemma1
                           / end-lemma3 /)
              ◃/ ap (ap from) (To.glue-β (left (f₂₁ c))) / ap (ap from) (! (To.glue-β (right (f₂₃ c)))) /)

         =⟨ thing (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                       ∙□-o/ ∘-ap from left (glue (f₂₁ c)) ∙ I∙₀.glue-β (f₂₁ c)
                           / ! (∘-ap from right (glue (f₂₃ c)) ∙ I∙₄.glue-β (f₂₃ c)) /
                       ∙□-i/ ! end-lemma1
                           / end-lemma3 /) (ap (ap from) (To.glue-β (left (f₂₁ c)))) (ap (ap from) (! (To.glue-β (right (f₂₃ c))))) ⟩

    ↓-='-out (apd (glue {d = v-h-span}) (glue c))
    ∙□-o/ ∘-ap from left (glue (f₂₁ c)) ∙ I∙₀.glue-β (f₂₁ c)
        / ! (∘-ap from right (glue (f₂₃ c)) ∙ I∙₄.glue-β (f₂₃ c)) /
    ∙□-i/ ! end-lemma1
        / end-lemma3 /
    ∙□-o/ ap (ap from) (To.glue-β (left (f₂₁ c))) / ap (ap from) (! (To.glue-β (right (f₂₃ c)))) /

         =⟨ ch (↓-='-out (apd (glue {d = v-h-span}) (glue c))) (∘-ap from left (glue (f₂₁ c)))
               (ap-∘ from left (glue (f₂₁ c))) (!-∘-ap from left (glue (f₂₁ c))) (I∙₀.glue-β (f₂₁ c)) (∘-ap from right (glue (f₂₃ c)))
               (ap-∘ from right (glue (f₂₃ c))) (!-∘-ap from right (glue (f₂₃ c))) (I∙₄.glue-β (f₂₃ c)) (! end-lemma1) end-lemma3
               (ap (ap from) (To.glue-β (left (f₂₁ c)))) (! (To.glue-β (left (f₂₁ c))) |in-ctx ap from) (!-ap (ap from) (To.glue-β (left (f₂₁ c)))) (ap (ap from) (! (To.glue-β (right (f₂₃ c))))) ⟩

    ↓-='-out (apd (glue {d = v-h-span}) (glue c))
    ∙□-i/ ! end-lemma1
        / end-lemma3 /
    ∙□-o/ ! (from-to-g-l (f₂₁ c))
        / from-to-g-r (f₂₃ c) / ∎  where

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
