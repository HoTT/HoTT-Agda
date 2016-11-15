{-# OPTIONS --without-K #-}

--open import HoTT
open import homotopy.3x3.PushoutPushout
open import homotopy.3x3.Transpose
import homotopy.3x3.To as To
import homotopy.3x3.From as From
open import homotopy.3x3.Common

module homotopy.3x3.FromTo2 {i} (d : Span^2 {i}) where

open Span^2 d
open M d hiding (Pushout^2)
open M (transpose d) using () renaming (module F₁∙ to F∙₁; f₁∙ to f∙₁;
                                        module F₃∙ to F∙₃; f₃∙ to f∙₃;
                                        v-h-span to h-v-span)
open M using (Pushout^2)

open To d
open From d

open import homotopy.3x3.FromToInit d

module M2 (c : A₂₂) where

  coh : ∀ {i} {A : Type i} {a b c d : A}
    {p q : a == b} (α : p == q)
    {v w : b == d} {β β' : w == v} (eqβ : β == β')
    {t u : a == c} {ε ε' : u == t} (eqε : ε == ε')
    {r s : c == d} (ζ : r == s)
    (γ : (q , v =□ t , s))
    (δ : (p , w =□ u , r))
    (eq : γ == δ ∙□-i/ ! β' / ε' / ∙□-o/ ! α / ζ /)
    → (α , β , γ =□□ δ , ε , ζ)
  coh idp {β = idp} idp {ε = idp} idp idp _ _ x = x

  end-lemma1 : ap (right ∘ f₃∙) (glue c) == ap (from ∘ i₄∙ ∘ f₃∙) (glue c) :> E∙₂Red.T-lhs c
  end-lemma1 =
    ap (right ∘ f₃∙) (glue c)
         =⟨ ap-∘ right f₃∙ (glue c) ⟩
    ap right (ap f₃∙ (glue c))
         =⟨ ap (ap right) (F₃∙.glue-β c) ⟩
    ap right (ap left (H₃₁ c) ∙ glue (f₃₂ c) ∙ ap right (H₃₃ c))
         =⟨ ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c) ⟩
    ap (right ∘ left) (H₃₁ c) ∙ ap right (glue (f₃₂ c)) ∙ ap (right ∘ right) (H₃₃ c)
         =⟨ ! (from-to-r-g (f₃₂ c)) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)) ⟩
    ap (right ∘ left) (H₃₁ c) ∙ (ap (from ∘ i₄∙) (glue (f₃₂ c))) ∙ ap (right ∘ right) (H₃₃ c)
         =⟨ ! (ap-∙∙`∘`∘ (from ∘ i₄∙) left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)) ⟩
    ap (from ∘ i₄∙) (ap left (H₃₁ c) ∙ glue (f₃₂ c) ∙ ap right (H₃₃ c))
         =⟨ ! (ap (ap (from ∘ i₄∙)) (F₃∙.glue-β c)) ⟩
    ap (from ∘ i₄∙) (ap f₃∙ (glue c))
         =⟨ ∘-ap (from ∘ i₄∙) f₃∙ (glue c) ⟩
    ap (from ∘ i₄∙ ∘ f₃∙) (glue c) ∎

  lemma1 : ↓-='-out (apd (from-to-r ∘ f₃∙) (glue c)) == end-lemma1
  lemma1 =
    ↓-='-out (apd (from-to-r ∘ f₃∙) (glue c))

         =⟨ apd-∘'' from-to-r f₃∙ (glue c) (F₃∙.glue-β c) |in-ctx ↓-='-out ⟩

    ↓-='-out (↓-ap-out= (λ b → from (to (right b)) == right b) f₃∙ (glue c) (F₃∙.glue-β c) (apd from-to-r (ap left (H₃₁ c) ∙ glue (f₃₂ c) ∙ ap right (H₃₃ c))))

         =⟨ apd-∙∙`∘`∘ from-to-r left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c) |in-ctx (λ u → ↓-='-out (↓-ap-out= (λ b → from (to (right b)) == right b) f₃∙ (glue c) (F₃∙.glue-β c) u)) ⟩

    ↓-='-out (↓-ap-out= (λ b → from (to (right b)) == right b) f₃∙ (glue c) (F₃∙.glue-β c) (↓-ap-in _ _ (apd (λ _ → idp) (H₃₁ c)) ∙ᵈ apd from-to-r (glue (f₃₂ c)) ∙ᵈ ↓-ap-in _ _  (apd (λ _ → idp) (H₃₃ c))))

         =⟨ FromToR.glue-β (f₃₂ c) |in-ctx (λ u → ↓-='-out (↓-ap-out= (λ b → from (to (right b)) == right b) f₃∙ (glue c) (F₃∙.glue-β c)
                                                                      (↓-ap-in _ _ (apd (λ _ → idp) (H₃₁ c)) ∙ᵈ u ∙ᵈ ↓-ap-in _ _  (apd (λ _ → idp) (H₃₃ c))))) ⟩

    ↓-='-out (↓-ap-out= (λ b → from (to (right b)) == right b) f₃∙ (glue c) (F₃∙.glue-β c)
                        (↓-ap-in _ _ (apd (λ _ → idp) (H₃₁ c)) ∙ᵈ ↓-='-in' (! (from-to-r-g (f₃₂ c))) ∙ᵈ ↓-ap-in _ _  (apd (λ _ → idp) (H₃₃ c))))

         =⟨ lemma-a _ f₃∙ (glue c) (F₃∙.glue-β c) _ ⟩

    ↓-='-out (↓-ap-in _ _ (apd (λ x → idp {a = right (left x)}) (H₃₁ c)) ∙ᵈ ↓-='-in' (! (from-to-r-g (f₃₂ c))) ∙ᵈ ↓-ap-in _ _  (apd (λ _ → idp) (H₃₃ c)))
    ∙□-i/ ap-∘ right f₃∙ (glue c) ∙ ap (ap right) (F₃∙.glue-β c)
        / ! (ap (ap (from ∘ i₄∙)) (F₃∙.glue-β c)) ∙ ∘-ap (from ∘ i₄∙) f₃∙ (glue c) /

         =⟨ lemma-b (glue (f₃₂ c)) (apd (λ _ → idp) (H₃₁ c)) (! (from-to-r-g (f₃₂ c))) (apd (λ _ → idp) (H₃₃ c)) |in-ctx (λ u → u ∙□-i/ ap-∘ right f₃∙ (glue c) ∙ ap (ap right) (F₃∙.glue-β c)
                                      / ! (ap (ap (from ∘ i₄∙)) (F₃∙.glue-β c)) ∙ ∘-ap (from ∘ i₄∙) f₃∙ (glue c) /) ⟩

    (↓-='-out (apd (λ x → idp {a = right (left x)}) (H₃₁ c))
    ∙□h ((! (from-to-r-g (f₃₂ c)))
    ∙□h (↓-='-out (apd (λ _ → idp) (H₃₃ c)))))
    ∙□-i/ ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)
        / ! (ap-∙∙`∘`∘ (from ∘ i₄∙) left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)) /
    ∙□-i/ ap-∘ right f₃∙ (glue c) ∙ ap (ap right) (F₃∙.glue-β c)
        / ! (ap (ap (from ∘ i₄∙)) (F₃∙.glue-β c)) ∙ ∘-ap (from ∘ i₄∙) f₃∙ (glue c) /

         =⟨ coh3 |in-ctx (λ u → u
                                ∙□-i/ ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)
                                    / ! (ap-∙∙`∘`∘ (from ∘ i₄∙) left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)) /
                                ∙□-i/ ap-∘ right f₃∙ (glue c) ∙ ap (ap right) (F₃∙.glue-β c)
                                    / ! (ap (ap (from ∘ i₄∙)) (F₃∙.glue-β c)) ∙ ∘-ap (from ∘ i₄∙) f₃∙ (glue c) /) ⟩

    ((! (from-to-r-g (f₃₂ c))) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
    ∙□-i/ ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)
        / ! (ap-∙∙`∘`∘ (from ∘ i₄∙) left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)) /
    ∙□-i/ ap-∘ right f₃∙ (glue c) ∙ ap (ap right) (F₃∙.glue-β c)
        / ! (ap (ap (from ∘ i₄∙)) (F₃∙.glue-β c)) ∙ ∘-ap (from ∘ i₄∙) f₃∙ (glue c) /

         =⟨ coh' ⟩
    end-lemma1 ∎  where

      coh' : ∀ {i} {A : Type i} {x y : A} {a b c d e f g h : x == y} {p : a == b} {q : b == c}
        {r : c == d} {s : d == e} {t : e == f} {u : f == g} {v : g == h}
        → (s ∙□-i/ r / t / ∙□-i/ p ∙ q / u ∙ v /) == (a =⟨ p ⟩ b =⟨ q ⟩ c =⟨ r ⟩ d =⟨ s ⟩ e =⟨ t ⟩ f =⟨ u ⟩ g =⟨ v ⟩ h ∎)
      coh' {p = idp} {idp} {idp} {idp} {idp} {idp} {idp} = idp

      coh2 : ∀ {i j} {A : Type i} {B : Type j} {f : A → B} {x y : A} {p : x == y}
        → ↓-='-out (apd (λ x → idp {a = f x}) p) == idp {a = ap f p}
      coh2 {p = idp} = idp

      coh3 : (↓-='-out (apd (λ x → idp {a = right (left x)}) (H₃₁ c))
              ∙□h ((! (from-to-r-g (f₃₂ c)))
              ∙□h (↓-='-out (apd (λ _ → idp) (H₃₃ c))))) == ((! (from-to-r-g (f₃₂ c))) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
      coh3 =
        ↓-='-out (apd (λ x → idp {a = right (left x)}) (H₃₁ c))
        ∙□h ((! (from-to-r-g (f₃₂ c)))
        ∙□h (↓-='-out (apd (λ _ → idp) (H₃₃ c))))

             =⟨ coh2 {f = right ∘ left} {p = H₃₁ c} |in-ctx (λ u → u ∙□h ((! (from-to-r-g (f₃₂ c))) ∙□h (↓-='-out (apd (λ _ → idp) (H₃₃ c))))) ⟩

        idp {a = ap (right ∘ left) (H₃₁ c)} ∙□h ((! (from-to-r-g (f₃₂ c)))
            ∙□h (↓-='-out (apd (λ _ → idp) (H₃₃ c))))

             =⟨ coh2 {f = right ∘ right} {p = H₃₃ c} |in-ctx (λ u → idp {a = ap (right ∘ left) (H₃₁ c)} ∙□h ((! (from-to-r-g (f₃₂ c))) ∙□h u)) ⟩

        idp {a = ap (right ∘ left) (H₃₁ c)} ∙□h ((! (from-to-r-g (f₃₂ c))) ∙□h idp {a = ap (right ∘ right) (H₃₃ c)})

              =⟨ coh4 (ap (right ∘ left) (H₃₁ c)) (ap (right ∘ right) (H₃₃ c)) (! (from-to-r-g (f₃₂ c))) ⟩

        ((! (from-to-r-g (f₃₂ c))) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c))) ∎  where

          coh4 : ∀ {i} {A : Type i} {x y z t : A} (p : x == y) (q : z == t) {s t : y == z} (r : s == t)
            → (idp {a = p} ∙□h (r ∙□h idp {a = q})) == (r |in-ctx (λ u → p ∙ u ∙ q))
          coh4 idp idp idp = idp

  end-lemma3 : ap (left ∘ f₁∙) (glue c) == ap (from ∘ i₀∙ ∘ f₁∙) (glue c)
  end-lemma3 =
    ap (left ∘ f₁∙) (glue c)
         =⟨ ap-∘ left f₁∙ (glue c) ⟩
    ap left (ap f₁∙ (glue c))
         =⟨ ap (ap left) (F₁∙.glue-β c) ⟩
    ap left (ap left (H₁₁ c) ∙ glue (f₁₂ c) ∙ ap right (H₁₃ c))
         =⟨ ap-∙∙`∘`∘ left left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c) ⟩
    ap (left ∘ left) (H₁₁ c) ∙ ap left (glue (f₁₂ c)) ∙ ap (left ∘ right) (H₁₃ c)
         =⟨ ! (from-to-l-g (f₁₂ c)) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (left ∘ right) (H₁₃ c)) ⟩
    ap (left ∘ left) (H₁₁ c) ∙ (ap (from ∘ i₀∙) (glue (f₁₂ c))) ∙ ap (left ∘ right) (H₁₃ c)
         =⟨ ! (ap-∙∙`∘`∘ (from ∘ i₀∙) left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c)) ⟩
    ap (from ∘ i₀∙) (ap left (H₁₁ c) ∙ glue (f₁₂ c) ∙ ap right (H₁₃ c))
         =⟨ ! (ap (ap (from ∘ i₀∙)) (F₁∙.glue-β c)) ⟩
    ap (from ∘ i₀∙) (ap f₁∙ (glue c))
         =⟨ ∘-ap (from ∘ i₀∙) f₁∙ (glue c) ⟩
    ap (from ∘ i₀∙ ∘ f₁∙) (glue c) ∎

  lemma3 : ↓-='-out (apd (from-to-l ∘ f₁∙) (glue c)) == end-lemma3
  lemma3 =
    ↓-='-out (apd (from-to-l ∘ f₁∙) (glue c))

      =⟨ apd-∘'' from-to-l f₁∙ (glue c) (F₁∙.glue-β c) |in-ctx ↓-='-out ⟩

    ↓-='-out (↓-ap-out= (λ b → from (to (left b)) == left b) f₁∙ (glue c) (F₁∙.glue-β c) (apd from-to-l (ap left (H₁₁ c) ∙ glue (f₁₂ c) ∙ ap right (H₁₃ c))))

      =⟨ lemma-a _ f₁∙ (glue c) (F₁∙.glue-β c) (apd from-to-l (ap left (H₁₁ c) ∙ glue (f₁₂ c) ∙ ap right (H₁₃ c))) ⟩

    ↓-='-out (apd from-to-l (ap left (H₁₁ c) ∙ glue (f₁₂ c) ∙ ap right (H₁₃ c)))
    ∙□-i/ ap-∘ left f₁∙ (glue c) ∙ ap (ap left) (F₁∙.glue-β c) / ! (ap (ap (from ∘ to ∘ left)) (F₁∙.glue-β c)) ∙ ∘-ap (from ∘ to ∘ left) f₁∙ (glue c) /

      =⟨ apd-∙∙`∘`∘ from-to-l left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c) |in-ctx
         (λ u → ↓-='-out u ∙□-i/ ap-∘ left f₁∙ (glue c) ∙ ap (ap left) (F₁∙.glue-β c) / ! (ap (ap (from ∘ to ∘ left)) (F₁∙.glue-β c)) ∙ ∘-ap (from ∘ to ∘ left) f₁∙ (glue c) /) ⟩

    ↓-='-out (↓-ap-in _ _ (apd (λ _ → idp) (H₁₁ c)) ∙ᵈ apd from-to-l (glue (f₁₂ c)) ∙ᵈ ↓-ap-in _ _ (apd (λ _ → idp) (H₁₃ c)))
    ∙□-i/ ap-∘ left f₁∙ (glue c) ∙ ap (ap left) (F₁∙.glue-β c) / ! (ap (ap (from ∘ to ∘ left)) (F₁∙.glue-β c)) ∙ ∘-ap (from ∘ to ∘ left) f₁∙ (glue c) /

      =⟨ FromToL.glue-β (f₁₂ c) |in-ctx (λ u → ↓-='-out (↓-ap-in _ _ (apd (λ _ → idp) (H₁₁ c)) ∙ᵈ u ∙ᵈ ↓-ap-in _ _ (apd (λ _ → idp) (H₁₃ c)))
         ∙□-i/ ap-∘ left f₁∙ (glue c) ∙ ap (ap left) (F₁∙.glue-β c) / ! (ap (ap (from ∘ to ∘ left)) (F₁∙.glue-β c)) ∙ ∘-ap (from ∘ to ∘ left) f₁∙ (glue c) /) ⟩

    ↓-='-out (↓-ap-in _ _ (apd (λ _ → idp) (H₁₁ c)) ∙ᵈ ↓-='-in' (! (from-to-l-g (f₁₂ c))) ∙ᵈ ↓-ap-in _ _ (apd (λ _ → idp) (H₁₃ c)))
    ∙□-i/ ap-∘ left f₁∙ (glue c) ∙ ap (ap left) (F₁∙.glue-β c) / ! (ap (ap (from ∘ to ∘ left)) (F₁∙.glue-β c)) ∙ ∘-ap (from ∘ to ∘ left) f₁∙ (glue c) /

      =⟨ lemma-b (glue (f₁₂ c)) (apd (λ _ → idp) (H₁₁ c)) (! (from-to-l-g (f₁₂ c))) (apd (λ _ → idp) (H₁₃ c))
         |in-ctx (λ u → u ∙□-i/ ap-∘ left f₁∙ (glue c) ∙ ap (ap left) (F₁∙.glue-β c) / ! (ap (ap (from ∘ to ∘ left)) (F₁∙.glue-β c)) ∙ ∘-ap (from ∘ to ∘ left) f₁∙ (glue c) /) ⟩

    (↓-='-out (apd (λ _ → idp) (H₁₁ c)) ∙□h ((! (from-to-l-g (f₁₂ c))) ∙□h ↓-='-out (apd (λ _ → idp) (H₁₃ c))))
    ∙□-i/ ap-∙∙`∘`∘ left left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c) / ! (ap-∙∙`∘`∘ (from ∘ i₀∙) left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c)) /
    ∙□-i/ ap-∘ left f₁∙ (glue c) ∙ ap (ap left) (F₁∙.glue-β c) / ! (ap (ap (from ∘ to ∘ left)) (F₁∙.glue-β c)) ∙ ∘-ap (from ∘ to ∘ left) f₁∙ (glue c) /

      =⟨ coh2 (left ∘ left) (left ∘ right) (H₁₁ c) (! (from-to-l-g (f₁₂ c))) (H₁₃ c) |in-ctx (λ u →
         u ∙□-i/ ap-∙∙`∘`∘ left left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c) / ! (ap-∙∙`∘`∘ (from ∘ i₀∙) left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c)) /
    ∙□-i/ ap-∘ left f₁∙ (glue c) ∙ ap (ap left) (F₁∙.glue-β c) / ! (ap (ap (from ∘ to ∘ left)) (F₁∙.glue-β c)) ∙ ∘-ap (from ∘ to ∘ left) f₁∙ (glue c) /) ⟩

    ((! (from-to-l-g (f₁₂ c))) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (left ∘ right) (H₁₃ c)))
    ∙□-i/ ap-∙∙`∘`∘ left left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c) / ! (ap-∙∙`∘`∘ (from ∘ i₀∙) left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c)) /
    ∙□-i/ ap-∘ left f₁∙ (glue c) ∙ ap (ap left) (F₁∙.glue-β c) / ! (ap (ap (from ∘ to ∘ left)) (F₁∙.glue-β c)) ∙ ∘-ap (from ∘ to ∘ left) f₁∙ (glue c) /

      =⟨ coh3 ⟩

    end-lemma3 ∎  where

      coh2 : ∀ {i i' j} {A : Type i} {A' : Type i'} {B : Type j} (f : A → B) (f' : A' → B)
             {a b : A} {a' b' : A'} (p : a == b) {s s' : f b == f' a'} (q : s == s') (r : a' == b')
             → (↓-='-out (apd (λ x → idp) p) ∙□h (q ∙□h (↓-='-out (apd (λ _ → idp) r))))
               == (q |in-ctx (λ u → ap f p ∙ u ∙ ap f' r))
      coh2 f f' idp idp idp = idp

      coh3 : ∀ {i} {A : Type i} {x y : A} {a b c d e f g h : x == y} {p : a == b} {q : b == c}
        {r : c == d} {s : d == e} {t : e == f} {u : f == g} {v : g == h}
        → (s ∙□-i/ r / t / ∙□-i/ p ∙ q / u ∙ v /) == (a =⟨ p ⟩ b =⟨ q ⟩ c =⟨ r ⟩ d =⟨ s ⟩ e =⟨ t ⟩ f =⟨ u ⟩ g =⟨ v ⟩ h ∎)
      coh3 {p = idp} {idp} {idp} {idp} {idp} {idp} {idp} = idp

{- Lemma 2 -}

  lemma2-7 =
    ↓-='-out (ap↓ (ap from) (apd (glue {d = h-v-span}) (glue c)))

         =⟨ from-glue-glue-β c |in-ctx ↓-='-out ⟩

    ↓-='-out (↓-='-in' (E∙₂Red.coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                                      ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /)
                       ∙□-i/ E∙₂Red.lhs-o c / E∙₂Red.rhs-o c /)
              ◃/ From.glue-β (left (f₁₂ c)) / ! (From.glue-β (right (f₃₂ c))) /)

         =⟨ thing _ (From.glue-β (left (f₁₂ c))) _ ⟩

    E∙₂Red.coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                   ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /)
    ∙□-i/ E∙₂Red.lhs-o c / E∙₂Red.rhs-o c /
    ∙□-o/ From.glue-β (left (f₁₂ c)) / ! (From.glue-β (right (f₃₂ c))) / ∎


  lemma2-6 =
    ap□ from (↓-='-out (apd (glue {d = h-v-span}) (glue c)))

         =⟨ ap□-↓-='-out-β _ _ from (apd (glue {d = h-v-span}) (glue c)) ⟩

    ↓-='-out (ap↓ (ap from) (apd (glue {d = h-v-span}) (glue c)))
    ∙□-i/ ∘-ap from (right ∘ f∙₃) (glue c) / ap-∘ from (left ∘ f∙₁) (glue c) /

         =⟨ lemma2-7 |in-ctx (λ u → (u ∙□-i/ ∘-ap from (right ∘ f∙₃) (glue c) / ap-∘ from (left ∘ f∙₁) (glue c) /)) ⟩

    E∙₂Red.coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                   ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /)
    ∙□-i/ E∙₂Red.lhs-o c / E∙₂Red.rhs-o c /
    ∙□-o/ From.glue-β (left (f₁₂ c)) / ! (From.glue-β (right (f₃₂ c))) /
    ∙□-i/ ∘-ap from (right ∘ f∙₃) (glue c) / ap-∘ from (left ∘ f∙₁) (glue c) / ∎

  lemma2-5 =
    ap□ from (↓-='-out (apd (glue {d = h-v-span}) (glue c))
              ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /)

         =⟨ ap□-∙□-i/ from _ (E₂∙Red.lhs-i c) _ ⟩

    ap□ from (↓-='-out (apd (glue {d = h-v-span}) (glue c)))
    ∙□-i/ ap (ap from) (E₂∙Red.lhs-i c) / ap (ap from) (E₂∙Red.rhs-i c) /

         =⟨ lemma2-6 |in-ctx (λ u → u ∙□-i/ ap (ap from) (E₂∙Red.lhs-i c) / ap (ap from) (E₂∙Red.rhs-i c) /) ⟩

    E∙₂Red.coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                   ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /)
    ∙□-i/ E∙₂Red.lhs-o c / E∙₂Red.rhs-o c /
    ∙□-o/ From.glue-β (left (f₁₂ c)) / ! (From.glue-β (right (f₃₂ c))) /
    ∙□-i/ ∘-ap from (right ∘ f∙₃) (glue c) / ap-∘ from (left ∘ f∙₁) (glue c) /
    ∙□-i/ ap (ap from) (E₂∙Red.lhs-i c) / ap (ap from) (E₂∙Red.rhs-i c) / ∎

  lemma2'-1 =
    E₂∙Red.ap-ap-coh-lhs-i c from ∙ ap (ap from) (E₂∙Red.lhs-i c) ∙ ∘-ap from (right ∘ f∙₃) (glue c) ∙ E∙₂Red.lhs-o c

         =⟨ eq1 {f = ap from}
                {q = ! (ap-∙∙!`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c))}
                { ! (F∙₃.glue-β c) |in-ctx (ap right)}
                {∘-ap right f∙₃ (glue c)}
                {p = E₂∙Red.ap-ap-coh-lhs-i c from}
                {∘-ap from (right ∘ f∙₃) (glue c)}
                {ap-∘ i∙₄ f∙₃ (glue c)}
                {F∙₃.glue-β c |in-ctx (ap i∙₄)}
                {ap-∙∙!`∘`∘ i∙₄ left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c)}
                {I∙₄.glue-β (f₂₃ c) |in-ctx (λ u → ap (left ∘ right) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c)))}
          ⟩

    (! (ap-∙∙!'`∘`∘ from (right ∘ left) (right ∘ right) (H₁₃ c) (ap right (glue (f₂₃ c))) (H₃₃ c))
     ∙ ap (ap from) (! (ap-∙∙!`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c)))
     ∙ (ap (ap from) (! (F∙₃.glue-β c) |in-ctx (ap right))
        ∙ (ap (ap from) (∘-ap right f∙₃ (glue c))
           ∙ ∘-ap from (right ∘ f∙₃) (glue c)
           ∙ ap-∘ i∙₄ f∙₃ (glue c))
        ∙ (F∙₃.glue-β c |in-ctx (ap i∙₄)))
     ∙ ap-∙∙!`∘`∘ i∙₄ left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c))
    ∙ (I∙₄.glue-β (f₂₃ c) |in-ctx (λ u → ap (left ∘ right) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c))))

         =⟨ ap-∘^3-coh from right f∙₃ (glue c) |in-ctx (λ u →
    (! (ap-∙∙!'`∘`∘ from (right ∘ left) (right ∘ right) (H₁₃ c) (ap right (glue (f₂₃ c))) (H₃₃ c))
     ∙ ap (ap from) (! (ap-∙∙!`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c)))
     ∙ (ap (ap from) (! (F∙₃.glue-β c) |in-ctx (ap right))
        ∙ u
        ∙ (F∙₃.glue-β c |in-ctx (ap i∙₄)))
     ∙ ap-∙∙!`∘`∘ i∙₄ left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c))
    ∙ (I∙₄.glue-β (f₂₃ c) |in-ctx (λ u → ap (left ∘ right) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c)))))
          ⟩

    (! (ap-∙∙!'`∘`∘ from (right ∘ left) (right ∘ right) (H₁₃ c) (ap right (glue (f₂₃ c))) (H₃₃ c))
     ∙ ap (ap from) (! (ap-∙∙!`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c)))
     ∙ (ap (ap from) (! (F∙₃.glue-β c) |in-ctx (ap right))
        ∙ ∘-ap from right (ap f∙₃ (glue c))
        ∙ (F∙₃.glue-β c |in-ctx (ap i∙₄)))
     ∙ ap-∙∙!`∘`∘ i∙₄ left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c))
    ∙ (I∙₄.glue-β (f₂₃ c) |in-ctx (λ u → ap (left ∘ right) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c))))

         =⟨ ap-∘-ap-coh from right (F∙₃.glue-β c) |in-ctx (λ u →
    (! (ap-∙∙!'`∘`∘ from (right ∘ left) (right ∘ right) (H₁₃ c) (ap right (glue (f₂₃ c))) (H₃₃ c))
     ∙ ap (ap from) (! (ap-∙∙!`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c)))
     ∙ u
     ∙ ap-∙∙!`∘`∘ i∙₄ left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c))
    ∙ (I∙₄.glue-β (f₂₃ c) |in-ctx (λ u → ap (left ∘ right) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c))))) ⟩

    (! (ap-∙∙!'`∘`∘ from (right ∘ left) (right ∘ right) (H₁₃ c) (ap right (glue (f₂₃ c))) (H₃₃ c))
     ∙ ap (ap from) (! (ap-∙∙!`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c)))
     ∙ ∘-ap from right (ap left (H₁₃ c) ∙ glue (f₂₃ c) ∙ ap right (! (H₃₃ c)))
     ∙ ap-∙∙!`∘`∘ i∙₄ left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c))
    ∙ (I∙₄.glue-β (f₂₃ c) |in-ctx (λ u → ap (left ∘ right) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c))))

         =⟨ ap-∘-ap-∙∙!`∘`∘-coh from right left right (H₁₃ c) (glue (f₂₃ c)) (H₃₃ c) |in-ctx (λ u →
             u ∙ (I∙₄.glue-β (f₂₃ c) |in-ctx (λ u → ap (left ∘ right) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c))))) ⟩

    (∘-ap from right (glue (f₂₃ c)) |in-ctx (λ u → ap (left ∘ right) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c))))
    ∙ (I∙₄.glue-β (f₂₃ c) |in-ctx (λ u → ap (left ∘ right) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c))))

         =⟨ ∙-|in-ctx (λ u → ap (left ∘ right) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c))) (∘-ap from right (glue (f₂₃ c))) (I∙₄.glue-β (f₂₃ c)) ⟩

    ((∘-ap from right (glue (f₂₃ c)) ∙ I∙₄.glue-β (f₂₃ c)) |in-ctx (λ u → ap (left ∘ right) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c)))) ∎

    where

      eq1 : ∀ {i j} {A : Type i} {B : Type j} {f : A → B} {a b c d : A}
        {q : a == b} {r : b == c} {s : c == d}
        {g h k l m n : B} {p : g == f a} {t : f d == h} {u : h == k}
        {v : k == l} {w : l == m} {x : m == n}
         → p ∙ ap f (_ =⟨ q ⟩ _ =⟨ r ⟩ _ =⟨ s ⟩ _ ∎) ∙ t
           ∙ (_ =⟨ u ⟩ _ =⟨ v ⟩ _ =⟨ w ⟩ _ =⟨ x ⟩ _ ∎)
         == (p ∙ ap f q ∙ (ap f r ∙ (ap f s ∙ t ∙ u) ∙ v) ∙ w) ∙ x
      eq1 {q = idp} {idp} {idp} {p = p} {idp} {idp} {idp} {idp} {idp} = ! (∙-unit-r (p ∙ idp))

  lemma2'-2 :
    E∙₂Red.rhs-o c
    ∙ ap-∘ from (left ∘ f∙₁) (glue c)
    ∙ ap (ap from) (E₂∙Red.rhs-i c)
    ∙ E₂∙Red.ap-ap-coh-rhs-i c from
    == (! (∘-ap from left (glue (f₂₁ c)) ∙ I∙₀.glue-β (f₂₁ c)) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c)))
  lemma2'-2 =
    E∙₂Red.rhs-o c ∙ ap-∘ from (left ∘ f∙₁) (glue c) ∙ ap (ap from) (E₂∙Red.rhs-i c) ∙ E₂∙Red.ap-ap-coh-rhs-i c from

      =⟨ eq1 {f = ap from}
             {p = ! (I∙₀.glue-β (f₂₁ c)) |in-ctx (λ u → (! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c)))}
             { ! (ap-!∙∙`∘`∘ i∙₀ left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c))}
             { ! (F∙₁.glue-β c) |in-ctx (λ u → ap i∙₀ u)}
             {∘-ap i∙₀ f∙₁ (glue c)}
             {ap-∘ from (left ∘ f∙₁) (glue c)}
             {ap-∘ left f∙₁ (glue c)}
             {F∙₁.glue-β c |in-ctx (ap left)}
             {ap-!∙∙`∘`∘ left left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c)}
             {ap-!'∙∙`∘`∘ from (left ∘ left) (left ∘ right) (H₁₁ c) (ap left (glue (f₂₁ c))) (H₃₁ c)}
       ⟩

    (! (I∙₀.glue-β (f₂₁ c)) |in-ctx (λ u → (! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c))))
    ∙ ((! (ap-!∙∙`∘`∘ i∙₀ left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c)))
       ∙ ((! (F∙₁.glue-β c) |in-ctx (λ u → ap i∙₀ u))
          ∙ (∘-ap i∙₀ f∙₁ (glue c)
             ∙ ap-∘ from (left ∘ f∙₁) (glue c)
             ∙ ap (ap from) (ap-∘ left f∙₁ (glue c)))
          ∙ ap (ap from) (F∙₁.glue-β c |in-ctx (ap left)))
       ∙ ap (ap from) (ap-!∙∙`∘`∘ left left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c))
       ∙ ap-!'∙∙`∘`∘ from (left ∘ left) (left ∘ right) (H₁₁ c) (ap left (glue (f₂₁ c))) (H₃₁ c))

      =⟨ ap-∘^3-coh' from left f∙₁ (glue c)
         |in-ctx (λ u → (! (I∙₀.glue-β (f₂₁ c)) |in-ctx (λ u → (! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c))))
    ∙ ((! (ap-!∙∙`∘`∘ i∙₀ left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c)))
       ∙ ((! (F∙₁.glue-β c) |in-ctx (λ u → ap i∙₀ u))
          ∙ u
          ∙ ap (ap from) (F∙₁.glue-β c |in-ctx (ap left)))
       ∙ ap (ap from) (ap-!∙∙`∘`∘ left left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c))
       ∙ ap-!'∙∙`∘`∘ from (left ∘ left) (left ∘ right) (H₁₁ c) (ap left (glue (f₂₁ c))) (H₃₁ c))) ⟩

    (! (I∙₀.glue-β (f₂₁ c)) |in-ctx (λ u → (! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c))))
    ∙ ((! (ap-!∙∙`∘`∘ i∙₀ left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c)))
       ∙ ((! (F∙₁.glue-β c) |in-ctx (ap i∙₀))
          ∙ ap-∘ from left (ap f∙₁ (glue c))
          ∙ ap (ap from) (F∙₁.glue-β c |in-ctx (ap left)))
       ∙ ap (ap from) (ap-!∙∙`∘`∘ left left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c))
       ∙ ap-!'∙∙`∘`∘ from (left ∘ left) (left ∘ right) (H₁₁ c) (ap left (glue (f₂₁ c))) (H₃₁ c))

      =⟨ ap-∘-ap-coh' from left (F∙₁.glue-β c)
         |in-ctx (λ u → (! (I∙₀.glue-β (f₂₁ c)) |in-ctx (λ u → (! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c))))
    ∙ ((! (ap-!∙∙`∘`∘ i∙₀ left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c)))
       ∙ u
       ∙ ap (ap from) (ap-!∙∙`∘`∘ left left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c))
       ∙ ap-!'∙∙`∘`∘ from (left ∘ left) (left ∘ right) (H₁₁ c) (ap left (glue (f₂₁ c))) (H₃₁ c))) ⟩

    (! (I∙₀.glue-β (f₂₁ c)) |in-ctx (λ u → (! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c))))
    ∙ ((! (ap-!∙∙`∘`∘ i∙₀ left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c)))
       ∙ ap-∘ from left (ap left (! (H₁₁ c)) ∙ glue (f₂₁ c) ∙ ap right (H₃₁ c))
       ∙ ap (ap from) (ap-!∙∙`∘`∘ left left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c))
       ∙ ap-!'∙∙`∘`∘ from (left ∘ left) (left ∘ right) (H₁₁ c) (ap left (glue (f₂₁ c))) (H₃₁ c))

      =⟨ ap-∘-ap-!∙∙`∘`∘-coh from left left right (H₁₁ c) (glue (f₂₁ c)) (H₃₁ c)
         |in-ctx (λ u → (! (I∙₀.glue-β (f₂₁ c)) |in-ctx (λ u → (! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c)))) ∙ u) ⟩

    (! (I∙₀.glue-β (f₂₁ c)) |in-ctx (λ u → (! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c))))
    ∙ (ap-∘ from left (glue (f₂₁ c)) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c)))

      =⟨ coh2 (glue (f₂₁ c)) (I∙₀.glue-β (f₂₁ c)) ⟩

    (! (∘-ap from left (glue (f₂₁ c)) ∙ I∙₀.glue-β (f₂₁ c)) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c))) ∎

    where

      eq1 : ∀ {i j} {A : Type i} {B : Type j} {f : A → B} {a b c d e : B} {k l m n : A} {o : B}
         {p : a == b} {q : b == c} {r : c == d} {s : d == e} {t : e == f k} {u : k == l}
         {v : l == m} {w : m == n} {x : f n == o}
         → (_ =⟨ p ⟩ _ =⟨ q ⟩ _ =⟨ r ⟩ _ =⟨ s ⟩ _ ∎) ∙ t ∙ ap f (_ =⟨ u ⟩ _ =⟨ v ⟩ _ =⟨ w ⟩ _ ∎) ∙ x
         == (p ∙ (q ∙ ((r ∙ (s ∙ t ∙ ap f u) ∙ ap f v) ∙ ap f w ∙ x)))
      eq1 {p = idp} {idp} {idp} {idp} {t = t} {idp} {idp} {idp} {idp} = ! (∙-unit-r (t ∙ idp)) ∙ ! (∙-unit-r ((t ∙ idp) ∙ idp))

      coh2 : ∀ {i j k l} {A : Type i} {B : Type j} {C : Type k} {D : Type l}
        {a a' : A} (q : a == a') {h : A → B} {g : B → C} {f : (g (h a) == g (h a')) → D} {r : g (h a) == g (h a')} (p : ap (g ∘ h) q == r)
        → ((! p) |in-ctx f) ∙ (ap-∘ g h q |in-ctx f) == (! (∘-ap g h q ∙ p) |in-ctx f)
      coh2 idp p = ∙-unit-r _

  lemma2-4' =
    ap□ from (↓-='-out (apd (glue {d = h-v-span}) (glue c))
              ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /)
    ∙□-i/ E₂∙Red.ap-ap-coh-lhs-i c from / E₂∙Red.ap-ap-coh-rhs-i c from /

         =⟨ lemma2-5 |in-ctx (λ u → u ∙□-i/ E₂∙Red.ap-ap-coh-lhs-i c from / E₂∙Red.ap-ap-coh-rhs-i c from /) ⟩

    E∙₂Red.coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                   ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /)
    ∙□-i/ E∙₂Red.lhs-o c / E∙₂Red.rhs-o c /
    ∙□-o/ From.glue-β (left (f₁₂ c)) / ! (From.glue-β (right (f₃₂ c))) /
    ∙□-i/ ∘-ap from (right ∘ f∙₃) (glue c) / ap-∘ from (left ∘ f∙₁) (glue c) /
    ∙□-i/ ap (ap from) (E₂∙Red.lhs-i c) / ap (ap from) (E₂∙Red.rhs-i c) /
    ∙□-i/ E₂∙Red.ap-ap-coh-lhs-i c from / E₂∙Red.ap-ap-coh-rhs-i c from /

         =⟨ assoc (E∙₂Red.coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                   ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /))
                   (E∙₂Red.lhs-o c) (∘-ap from (right ∘ f∙₃) (glue c)) (ap (ap from) (E₂∙Red.lhs-i c))
                   (E₂∙Red.ap-ap-coh-lhs-i c from) _ _ _ _ (From.glue-β (left (f₁₂ c))) _ ⟩

    E∙₂Red.coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                   ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /)
    ∙□-o/ From.glue-β (left (f₁₂ c)) / ! (From.glue-β (right (f₃₂ c))) /
    ∙□-i/ E₂∙Red.ap-ap-coh-lhs-i c from ∙ ap (ap from) (E₂∙Red.lhs-i c) ∙ ∘-ap from (right ∘ f∙₃) (glue c) ∙ E∙₂Red.lhs-o c
        / E∙₂Red.rhs-o c ∙ ap-∘ from (left ∘ f∙₁) (glue c) ∙ ap (ap from) (E₂∙Red.rhs-i c) ∙ E₂∙Red.ap-ap-coh-rhs-i c from /

         =⟨ ∙□-i/-rewrite (E∙₂Red.coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                   ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /)
    ∙□-o/ From.glue-β (left (f₁₂ c)) / ! (From.glue-β (right (f₃₂ c))) /) lemma2'-1 lemma2'-2 ⟩ -- rewrite

    E∙₂Red.coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                   ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /)
    ∙□-o/ From.glue-β (left (f₁₂ c)) / ! (From.glue-β (right (f₃₂ c))) /
    ∙□-i/ (∘-ap from right (glue (f₂₃ c)) ∙ I∙₄.glue-β (f₂₃ c)) |in-ctx (λ u → ap (left ∘ right) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c)))
        / (! (∘-ap from left (glue (f₂₁ c)) ∙ I∙₀.glue-β (f₂₁ c))) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c)) / ∎  where

      assoc : ∀ {i} {A : Type i} {a b b' c : A} {u u' : a == b} {v v1 v2 v3 v4 : b == c}
         {w w1 w2 w3 w4 : a == b'} {x x' : b' == c} (α : (u , v =□ w , x))
         (p1 : v1 == v) (p2 : v2 == v1) (p3 : v3 == v2) (p4 : v4 == v3)
         (q1 : w == w1) (q2 : w1 == w2) (q3 : w2 == w3) (q4 : w3 == w4)
         (r : u' == u) (s : x == x')
         → α ∙□-i/ p1 / q1 / ∙□-o/ r / s / ∙□-i/ p2 / q2 / ∙□-i/ p3 / q3 / ∙□-i/ p4 / q4 /
         == α ∙□-o/ r / s / ∙□-i/ p4 ∙ p3 ∙ p2 ∙ p1 / q1 ∙ q2 ∙ q3 ∙ q4 /
      assoc α idp idp idp idp idp idp idp idp idp idp = idp

  lemma2-4'' =
    E₂∙Red.ap-ap-coh c from (ap□ from (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                                       ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /)
                             ∙□-i/ E₂∙Red.ap-ap-coh-lhs-i c from / E₂∙Red.ap-ap-coh-rhs-i c from /)

         =⟨ lemma2-4' |in-ctx (E₂∙Red.ap-ap-coh c from) ⟩

    E₂∙Red.ap-ap-coh c from (E∙₂Red.coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                                            ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /)
                             ∙□-o/ From.glue-β (left (f₁₂ c)) / ! (From.glue-β (right (f₃₂ c))) /
                             ∙□-i/ (∘-ap from right (glue (f₂₃ c)) ∙ I∙₄.glue-β (f₂₃ c)) |in-ctx (λ u → ap (left ∘ right) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c)))
                                 / (! (∘-ap from left (glue (f₂₁ c)) ∙ I∙₀.glue-β (f₂₁ c))) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (right ∘ left) (H₃₁ c))/)

         =⟨ lemma (∘-ap from left (glue (f₂₁ c)) ∙ I∙₀.glue-β (f₂₁ c)) (From.glue-β (right (f₃₂ c))) (From.glue-β (left (f₁₂ c))) (∘-ap from right (glue (f₂₃ c)) ∙ I∙₄.glue-β (f₂₃ c))
                   (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                   ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /) ⟩

    ↓-='-out (apd (glue {d = v-h-span}) (glue c))
    ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /
    ∙□-o/ ∘-ap from left (glue (f₂₁ c)) ∙ I∙₀.glue-β (f₂₁ c) / ! (∘-ap from right (glue (f₂₃ c)) ∙ I∙₄.glue-β (f₂₃ c)) /
    ∙□-i/ (From.glue-β (right (f₃₂ c))) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c))
        / (! (From.glue-β (left (f₁₂ c)))) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (left ∘ right) (H₁₃ c)) / ∎

  lemma2-4 =
    ap□ from (E₂∙Red.coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                            ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /))

         =⟨ E₂∙Red.ap-ap-coh-β c from (↓-='-out (apd (glue {d = h-v-span}) (glue c)) ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /) ⟩

    E₂∙Red.ap-ap-coh c from (ap□ from (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                                       ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /)
                             ∙□-i/ E₂∙Red.ap-ap-coh-lhs-i c from / E₂∙Red.ap-ap-coh-rhs-i c from /)
    ∙□-i/ E₂∙Red.ap-ap-coh-lhs-o c from / E₂∙Red.ap-ap-coh-rhs-o c from /

         =⟨ lemma2-4'' |in-ctx (λ u → u ∙□-i/ E₂∙Red.ap-ap-coh-lhs-o c from / E₂∙Red.ap-ap-coh-rhs-o c from /) ⟩

    ↓-='-out (apd (glue {d = v-h-span}) (glue c))
    ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /
    ∙□-o/ ∘-ap from left (glue (f₂₁ c)) ∙ I∙₀.glue-β (f₂₁ c) / ! (∘-ap from right (glue (f₂₃ c)) ∙ I∙₄.glue-β (f₂₃ c)) /
    ∙□-i/ (From.glue-β (right (f₃₂ c))) |in-ctx (λ u → ap (right ∘ left) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c))
        / (! (From.glue-β (left (f₁₂ c)))) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (left ∘ right) (H₁₃ c)) /
    ∙□-i/ E₂∙Red.ap-ap-coh-lhs-o c from / E₂∙Red.ap-ap-coh-rhs-o c from / ∎
