{-# OPTIONS --without-K #-}

--open import HoTT
open import homotopy.3x3.PushoutPushout
open import homotopy.3x3.Transpose
import homotopy.3x3.To as To
import homotopy.3x3.From as From
open import homotopy.3x3.Common

module homotopy.3x3.ToFrom2 {i} (d : Span^2 {i}) where

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

  end-lemma1 : ap (right ∘ f∙₃) (glue c) == ap (to ∘ i∙₄ ∘ f∙₃) (glue c) :> E₂∙Red.T-lhs c
  end-lemma1 =
    ap (right ∘ f∙₃) (glue c)
         =⟨ ap-∘ right f∙₃ (glue c) ⟩
    ap right (ap f∙₃ (glue c))
         =⟨ ap (ap right) (F∙₃.glue-β c) ⟩
    ap right (ap left (H₁₃ c) ∙ glue (f₂₃ c) ∙ ap right (! (H₃₃ c)))
         =⟨ ap-∙∙`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c)) ⟩
    ap (right ∘ left) (H₁₃ c) ∙ ap right (glue (f₂₃ c)) ∙ ap (right ∘ right) (! (H₃₃ c))
         =⟨ ! (to-from-r-g (f₂₃ c)) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))) ⟩
    ap (right ∘ left) (H₁₃ c) ∙ (ap (to ∘ i∙₄) (glue (f₂₃ c))) ∙ ap (right ∘ right) (! (H₃₃ c))
         =⟨ ! (ap-∙∙`∘`∘ (to ∘ i∙₄) left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c))) ⟩
    ap (to ∘ i∙₄) (ap left (H₁₃ c) ∙ glue (f₂₃ c) ∙ ap right (! (H₃₃ c)))
         =⟨ ! (ap (ap (to ∘ i∙₄)) (F∙₃.glue-β c)) ⟩
    ap (to ∘ i∙₄) (ap f∙₃ (glue c))
         =⟨ ∘-ap (to ∘ i∙₄) f∙₃ (glue c) ⟩
    ap (to ∘ i∙₄ ∘ f∙₃) (glue c) ∎

  abstract
   lemma1 : ↓-='-out (apd (to-from-r ∘ f∙₃) (glue c)) == end-lemma1
   lemma1 = 
    ↓-='-out (apd (to-from-r ∘ f∙₃) (glue c))

         =⟨ apd-∘'' to-from-r f∙₃ (glue c) (F∙₃.glue-β c) |in-ctx ↓-='-out ⟩

    ↓-='-out (↓-ap-out= (λ b → to (from (right b)) == right b) f∙₃ (glue c) (F∙₃.glue-β c) (apd to-from-r (ap left (H₁₃ c) ∙ glue (f₂₃ c) ∙ ap right (! (H₃₃ c)))))

         =⟨ apd-∙∙`∘`∘ to-from-r left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c)) |in-ctx (λ u → ↓-='-out (↓-ap-out= (λ b → to (from (right b)) == right b) f∙₃ (glue c) (F∙₃.glue-β c) u)) ⟩

    ↓-='-out (↓-ap-out= (λ b → to (from (right b)) == right b) f∙₃ (glue c) (F∙₃.glue-β c) (↓-ap-in _ _ (apd (λ _ → idp) (H₁₃ c)) ∙ᵈ apd to-from-r (glue (f₂₃ c)) ∙ᵈ ↓-ap-in _ _  (apd (λ _ → idp) (! (H₃₃ c)))))

         =⟨ ToFromR.glue-β (f₂₃ c) |in-ctx (λ u → ↓-='-out (↓-ap-out= (λ b → to (from (right b)) == right b) f∙₃ (glue c) (F∙₃.glue-β c)
                                                                      (↓-ap-in _ _ (apd (λ _ → idp) (H₁₃ c)) ∙ᵈ u ∙ᵈ ↓-ap-in _ _  (apd (λ _ → idp) (! (H₃₃ c)))))) ⟩

    ↓-='-out (↓-ap-out= (λ b → to (from (right b)) == right b) f∙₃ (glue c) (F∙₃.glue-β c)
                        (↓-ap-in _ _ (apd (λ _ → idp) (H₁₃ c)) ∙ᵈ ↓-='-in (! (to-from-r-g (f₂₃ c))) ∙ᵈ ↓-ap-in _ _  (apd (λ _ → idp) (! (H₃₃ c)))))

         =⟨ lemma-a _ f∙₃ (glue c) (F∙₃.glue-β c) _ ⟩

    ↓-='-out (↓-ap-in _ _ (apd (λ x → idp {a = right (left x)}) (H₁₃ c)) ∙ᵈ ↓-='-in (! (to-from-r-g (f₂₃ c))) ∙ᵈ ↓-ap-in _ _  (apd (λ _ → idp) (! (H₃₃ c))))
    ∙□-i/ ap-∘ right f∙₃ (glue c) ∙ ap (ap right) (F∙₃.glue-β c)
        / ! (ap (ap (to ∘ i∙₄)) (F∙₃.glue-β c)) ∙ ∘-ap (to ∘ i∙₄) f∙₃ (glue c) /

         =⟨ lemma-b (glue (f₂₃ c)) (apd (λ _ → idp) (H₁₃ c)) (! (to-from-r-g (f₂₃ c))) (apd (λ _ → idp) (! (H₃₃ c))) |in-ctx (λ u → u ∙□-i/ ap-∘ right f∙₃ (glue c) ∙ ap (ap right) (F∙₃.glue-β c)
                                      / ! (ap (ap (to ∘ i∙₄)) (F∙₃.glue-β c)) ∙ ∘-ap (to ∘ i∙₄) f∙₃ (glue c) /) ⟩

    (↓-='-out (apd (λ x → idp {a = right (left x)}) (H₁₃ c))
    ∙□h ((! (to-from-r-g (f₂₃ c)))
    ∙□h (↓-='-out (apd (λ _ → idp) (! (H₃₃ c))))))
    ∙□-i/ ap-∙∙`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c))
        / ! (ap-∙∙`∘`∘ (to ∘ i∙₄) left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c))) /
    ∙□-i/ ap-∘ right f∙₃ (glue c) ∙ ap (ap right) (F∙₃.glue-β c)
        / ! (ap (ap (to ∘ i∙₄)) (F∙₃.glue-β c)) ∙ ∘-ap (to ∘ i∙₄) f∙₃ (glue c) /

         =⟨ coh3 |in-ctx (λ u → u
                                ∙□-i/ ap-∙∙`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c))
                                    / ! (ap-∙∙`∘`∘ (to ∘ i∙₄) left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c))) /
                                ∙□-i/ ap-∘ right f∙₃ (glue c) ∙ ap (ap right) (F∙₃.glue-β c)
                                    / ! (ap (ap (to ∘ i∙₄)) (F∙₃.glue-β c)) ∙ ∘-ap (to ∘ i∙₄) f∙₃ (glue c) /) ⟩

    ((! (to-from-r-g (f₂₃ c))) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
    ∙□-i/ ap-∙∙`∘`∘ right left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c))
        / ! (ap-∙∙`∘`∘ (to ∘ i∙₄) left right (H₁₃ c) (glue (f₂₃ c)) (! (H₃₃ c))) /
    ∙□-i/ ap-∘ right f∙₃ (glue c) ∙ ap (ap right) (F∙₃.glue-β c)
        / ! (ap (ap (to ∘ i∙₄)) (F∙₃.glue-β c)) ∙ ∘-ap (to ∘ i∙₄) f∙₃ (glue c) /

         =⟨ coh' ⟩
    end-lemma1 ∎  where

      coh' : ∀ {i} {A : Type i} {x y : A} {a b c d e f g h : x == y} {p : a == b} {q : b == c}
        {r : c == d} {s : d == e} {t : e == f} {u : f == g} {v : g == h}
        → (s ∙□-i/ r / t / ∙□-i/ p ∙ q / u ∙ v /) == (a =⟨ p ⟩ b =⟨ q ⟩ c =⟨ r ⟩ d =⟨ s ⟩ e =⟨ t ⟩ f =⟨ u ⟩ g =⟨ v ⟩ h ∎)
      coh' {p = idp} {idp} {idp} {idp} {idp} {idp} {idp} = idp

      coh2 : ∀ {i j} {A : Type i} {B : Type j} {f : A → B} {x y : A} {p : x == y}
        → ↓-='-out (apd (λ x → idp {a = f x}) p) == idp {a = ap f p}
      coh2 {p = idp} = idp

      coh3 : (↓-='-out (apd (λ x → idp {a = right (left x)}) (H₁₃ c))
              ∙□h ((! (to-from-r-g (f₂₃ c)))
              ∙□h (↓-='-out (apd (λ _ → idp) (! (H₃₃ c)))))) == ((! (to-from-r-g (f₂₃ c))) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c))))
      coh3 = 
        ↓-='-out (apd (λ x → idp {a = right (left x)}) (H₁₃ c))
        ∙□h ((! (to-from-r-g (f₂₃ c)))
        ∙□h (↓-='-out (apd (λ _ → idp) (! (H₃₃ c)))))

             =⟨ coh2 {f = right ∘ left} {p = H₁₃ c} |in-ctx (λ u → u ∙□h ((! (to-from-r-g (f₂₃ c))) ∙□h (↓-='-out (apd (λ _ → idp) (! (H₃₃ c)))))) ⟩

        idp {a = ap (right ∘ left) (H₁₃ c)} ∙□h ((! (to-from-r-g (f₂₃ c)))
            ∙□h (↓-='-out (apd (λ _ → idp) (! (H₃₃ c)))))

             =⟨ coh2 {f = right ∘ right} {p = ! (H₃₃ c)} |in-ctx (λ u → idp {a = ap (right ∘ left) (H₁₃ c)} ∙□h ((! (to-from-r-g (f₂₃ c))) ∙□h u)) ⟩

        idp {a = ap (right ∘ left) (H₁₃ c)} ∙□h ((! (to-from-r-g (f₂₃ c))) ∙□h idp {a = ap (right ∘ right) (! (H₃₃ c))})

              =⟨ coh4 (ap (right ∘ left) (H₁₃ c)) (ap (right ∘ right) (! (H₃₃ c))) (! (to-from-r-g (f₂₃ c))) ⟩

        ((! (to-from-r-g (f₂₃ c))) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ap (right ∘ right) (! (H₃₃ c)))) ∎  where

          coh4 : ∀ {i} {A : Type i} {x y z t : A} (p : x == y) (q : z == t) {s t : y == z} (r : s == t)
            → (idp {a = p} ∙□h (r ∙□h idp {a = q})) == (r |in-ctx (λ u → p ∙ u ∙ q))
          coh4 idp idp idp = idp

  end-lemma3 : ap (left ∘ f∙₁) (glue c) == ap (to ∘ i∙₀ ∘ f∙₁) (glue c)
  end-lemma3 =
    ap (left ∘ f∙₁) (glue c)
         =⟨ ap-∘ left f∙₁ (glue c) ⟩
    ap left (ap f∙₁ (glue c))
         =⟨ ap (ap left) (F∙₁.glue-β c) ⟩
    ap left (ap left (! (H₁₁ c)) ∙ glue (f₂₁ c) ∙ ap right (H₃₁ c))
         =⟨ ap-∙∙`∘`∘ left left right (! (H₁₁ c)) (glue (f₂₁ c)) (H₃₁ c) ⟩
    ap (left ∘ left) (! (H₁₁ c)) ∙ ap left (glue (f₂₁ c)) ∙ ap (left ∘ right) (H₃₁ c)
         =⟨ ! (to-from-l-g (f₂₁ c)) |in-ctx (λ u → ap (left ∘ left) (! (H₁₁ c)) ∙ u ∙ ap (left ∘ right) (H₃₁ c)) ⟩
    ap (left ∘ left) (! (H₁₁ c)) ∙ (ap (to ∘ i∙₀) (glue (f₂₁ c))) ∙ ap (left ∘ right) (H₃₁ c)
         =⟨ ! (ap-∙∙`∘`∘ (to ∘ i∙₀) left right (! (H₁₁ c)) (glue (f₂₁ c)) (H₃₁ c)) ⟩
    ap (to ∘ i∙₀) (ap left (! (H₁₁ c)) ∙ glue (f₂₁ c) ∙ ap right (H₃₁ c))
         =⟨ ! (ap (ap (to ∘ i∙₀)) (F∙₁.glue-β c)) ⟩
    ap (to ∘ i∙₀) (ap f∙₁ (glue c))
         =⟨ ∘-ap (to ∘ i∙₀) f∙₁ (glue c) ⟩
    ap (to ∘ i∙₀ ∘ f∙₁) (glue c) ∎

  lemma3 : ↓-='-out (apd (to-from-l ∘ f∙₁) (glue c)) == end-lemma3
  lemma3 =
    ↓-='-out (apd (to-from-l ∘ f∙₁) (glue c))

      =⟨ apd-∘'' to-from-l f∙₁ (glue c) (F∙₁.glue-β c) |in-ctx ↓-='-out ⟩

    ↓-='-out (↓-ap-out= (λ b → to (from (left b)) == left b) f∙₁ (glue c) (F∙₁.glue-β c) (apd to-from-l (ap left (! (H₁₁ c)) ∙ glue (f₂₁ c) ∙ ap right (H₃₁ c))))

      =⟨ lemma-a _ f∙₁ (glue c) (F∙₁.glue-β c) (apd to-from-l (ap left (! (H₁₁ c)) ∙ glue (f₂₁ c) ∙ ap right (H₃₁ c))) ⟩

    ↓-='-out (apd to-from-l (ap left (! (H₁₁ c)) ∙ glue (f₂₁ c) ∙ ap right (H₃₁ c)))
    ∙□-i/ ap-∘ left f∙₁ (glue c) ∙ ap (ap left) (F∙₁.glue-β c) / ! (ap (ap (to ∘ from ∘ left)) (F∙₁.glue-β c)) ∙ ∘-ap (to ∘ from ∘ left) f∙₁ (glue c) /

      =⟨ apd-∙∙`∘`∘ to-from-l left right (! (H₁₁ c)) (glue (f₂₁ c)) (H₃₁ c) |in-ctx
         (λ u → ↓-='-out u ∙□-i/ ap-∘ left f∙₁ (glue c) ∙ ap (ap left) (F∙₁.glue-β c) / ! (ap (ap (to ∘ from ∘ left)) (F∙₁.glue-β c)) ∙ ∘-ap (to ∘ from ∘ left) f∙₁ (glue c) /) ⟩

    ↓-='-out (↓-ap-in _ _ (apd (λ _ → idp) (! (H₁₁ c))) ∙ᵈ apd to-from-l (glue (f₂₁ c)) ∙ᵈ ↓-ap-in _ _ (apd (λ _ → idp) (H₃₁ c)))
    ∙□-i/ ap-∘ left f∙₁ (glue c) ∙ ap (ap left) (F∙₁.glue-β c) / ! (ap (ap (to ∘ from ∘ left)) (F∙₁.glue-β c)) ∙ ∘-ap (to ∘ from ∘ left) f∙₁ (glue c) /

      =⟨ ToFromL.glue-β (f₂₁ c) |in-ctx (λ u → ↓-='-out (↓-ap-in _ _ (apd (λ _ → idp) (! (H₁₁ c))) ∙ᵈ u ∙ᵈ ↓-ap-in _ _ (apd (λ _ → idp) (H₃₁ c)))
         ∙□-i/ ap-∘ left f∙₁ (glue c) ∙ ap (ap left) (F∙₁.glue-β c) / ! (ap (ap (to ∘ from ∘ left)) (F∙₁.glue-β c)) ∙ ∘-ap (to ∘ from ∘ left) f∙₁ (glue c) /) ⟩

    ↓-='-out (↓-ap-in _ _ (apd (λ _ → idp) (! (H₁₁ c))) ∙ᵈ ↓-='-in (! (to-from-l-g (f₂₁ c))) ∙ᵈ ↓-ap-in _ _ (apd (λ _ → idp) (H₃₁ c)))
    ∙□-i/ ap-∘ left f∙₁ (glue c) ∙ ap (ap left) (F∙₁.glue-β c) / ! (ap (ap (to ∘ from ∘ left)) (F∙₁.glue-β c)) ∙ ∘-ap (to ∘ from ∘ left) f∙₁ (glue c) /

      =⟨ lemma-b (glue (f₂₁ c)) (apd (λ _ → idp) (! (H₁₁ c))) (! (to-from-l-g (f₂₁ c))) (apd (λ _ → idp) (H₃₁ c))
         |in-ctx (λ u → u ∙□-i/ ap-∘ left f∙₁ (glue c) ∙ ap (ap left) (F∙₁.glue-β c) / ! (ap (ap (to ∘ from ∘ left)) (F∙₁.glue-β c)) ∙ ∘-ap (to ∘ from ∘ left) f∙₁ (glue c) /) ⟩

    (↓-='-out (apd (λ _ → idp) (! (H₁₁ c))) ∙□h ((! (to-from-l-g (f₂₁ c))) ∙□h ↓-='-out (apd (λ _ → idp) (H₃₁ c))))
    ∙□-i/ ap-∙∙`∘`∘ left left right (! (H₁₁ c)) (glue (f₂₁ c)) (H₃₁ c) / ! (ap-∙∙`∘`∘ (to ∘ i∙₀) left right (! (H₁₁ c)) (glue (f₂₁ c)) (H₃₁ c)) /
    ∙□-i/ ap-∘ left f∙₁ (glue c) ∙ ap (ap left) (F∙₁.glue-β c) / ! (ap (ap (to ∘ from ∘ left)) (F∙₁.glue-β c)) ∙ ∘-ap (to ∘ from ∘ left) f∙₁ (glue c) /

      =⟨ coh2 (left ∘ left) (left ∘ right) (! (H₁₁ c)) (! (to-from-l-g (f₂₁ c))) (H₃₁ c) |in-ctx (λ u →
         u ∙□-i/ ap-∙∙`∘`∘ left left right (! (H₁₁ c)) (glue (f₂₁ c)) (H₃₁ c) / ! (ap-∙∙`∘`∘ (to ∘ i∙₀) left right (! (H₁₁ c)) (glue (f₂₁ c)) (H₃₁ c)) /
    ∙□-i/ ap-∘ left f∙₁ (glue c) ∙ ap (ap left) (F∙₁.glue-β c) / ! (ap (ap (to ∘ from ∘ left)) (F∙₁.glue-β c)) ∙ ∘-ap (to ∘ from ∘ left) f∙₁ (glue c) /) ⟩

    ((! (to-from-l-g (f₂₁ c))) |in-ctx (λ u → ap (left ∘ left) (! (H₁₁ c)) ∙ u ∙ ap (left ∘ right) (H₃₁ c)))
    ∙□-i/ ap-∙∙`∘`∘ left left right (! (H₁₁ c)) (glue (f₂₁ c)) (H₃₁ c) / ! (ap-∙∙`∘`∘ (to ∘ i∙₀) left right (! (H₁₁ c)) (glue (f₂₁ c)) (H₃₁ c)) /
    ∙□-i/ ap-∘ left f∙₁ (glue c) ∙ ap (ap left) (F∙₁.glue-β c) / ! (ap (ap (to ∘ from ∘ left)) (F∙₁.glue-β c)) ∙ ∘-ap (to ∘ from ∘ left) f∙₁ (glue c) /

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
    ↓-='-out (ap↓ (ap to) (apd (glue {d = v-h-span}) (glue c)))

         =⟨ to-glue-glue-β c |in-ctx ↓-='-out ⟩

    ↓-='-out (↓-='-in (E₂∙Red.coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                                      ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /)
                       ∙□-i/ E₂∙Red.lhs-o c / E₂∙Red.rhs-o c /)
              ◃/ To.glue-β (left (f₂₁ c)) / ! (To.glue-β (right (f₂₃ c))) /)

         =⟨ thing _ (To.glue-β (left (f₂₁ c))) _ ⟩

    E₂∙Red.coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                   ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /)
    ∙□-i/ E₂∙Red.lhs-o c / E₂∙Red.rhs-o c /
    ∙□-o/ To.glue-β (left (f₂₁ c)) / ! (To.glue-β (right (f₂₃ c))) / ∎


  lemma2-6 =
    ap□ to (↓-='-out (apd (glue {d = v-h-span}) (glue c)))

         =⟨ ap□-↓-='-out-β _ _ to (apd (glue {d = v-h-span}) (glue c)) ⟩

    ↓-='-out (ap↓ (ap to) (apd (glue {d = v-h-span}) (glue c)))
    ∙□-i/ ∘-ap to (right ∘ f₃∙) (glue c) / ap-∘ to (left ∘ f₁∙) (glue c) /

         =⟨ lemma2-7 |in-ctx (λ u → (u ∙□-i/ ∘-ap to (right ∘ f₃∙) (glue c) / ap-∘ to (left ∘ f₁∙) (glue c) /)) ⟩

    E₂∙Red.coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                   ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /)
    ∙□-i/ E₂∙Red.lhs-o c / E₂∙Red.rhs-o c /
    ∙□-o/ To.glue-β (left (f₂₁ c)) / ! (To.glue-β (right (f₂₃ c))) /
    ∙□-i/ ∘-ap to (right ∘ f₃∙) (glue c) / ap-∘ to (left ∘ f₁∙) (glue c) / ∎


  lemma2-5 =
    ap□ to (↓-='-out (apd (glue {d = v-h-span}) (glue c))
              ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /)

         =⟨ ap□-∙□-i/ to _ (E∙₂Red.lhs-i c) _ ⟩

    ap□ to (↓-='-out (apd (glue {d = v-h-span}) (glue c)))
    ∙□-i/ ap (ap to) (E∙₂Red.lhs-i c) / ap (ap to) (E∙₂Red.rhs-i c) /

         =⟨ lemma2-6 |in-ctx (λ u → u ∙□-i/ ap (ap to) (E∙₂Red.lhs-i c) / ap (ap to) (E∙₂Red.rhs-i c) /) ⟩

    E₂∙Red.coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                   ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /)
    ∙□-i/ E₂∙Red.lhs-o c / E₂∙Red.rhs-o c /
    ∙□-o/ To.glue-β (left (f₂₁ c)) / ! (To.glue-β (right (f₂₃ c))) /
    ∙□-i/ ∘-ap to (right ∘ f₃∙) (glue c) / ap-∘ to (left ∘ f₁∙) (glue c) /
    ∙□-i/ ap (ap to) (E∙₂Red.lhs-i c) / ap (ap to) (E∙₂Red.rhs-i c) / ∎

  lemma2'-1 =
    E∙₂Red.ap-ap-coh!-lhs-i c to ∙ ap (ap to) (E∙₂Red.lhs-i c) ∙ ∘-ap to (right ∘ f₃∙) (glue c) ∙ E₂∙Red.lhs-o c

         =⟨ eq1 {f = ap to}
                {q = ! (ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c))}
                { ! (ap (ap right) (F₃∙.glue-β c))}
                { ! (F₃∙.glue-β c) |in-ctx (ap right)}
                (!-ap (ap right) (F₃∙.glue-β c))
                {∘-ap right f₃∙ (glue c)}
                {p = E∙₂Red.ap-ap-coh!-lhs-i c to}
                {∘-ap to (right ∘ f₃∙) (glue c)}
                {ap-∘ i₄∙ f₃∙ (glue c)}
                {F₃∙.glue-β c |in-ctx (ap i₄∙)}
                {ap-∙∙`∘`∘ i₄∙ left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)}
                {I₄∙.glue-β (f₃₂ c) |in-ctx (λ u → ap (left ∘ right) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c))}
          ⟩

    (! (ap-∙∙`∘`∘ to (right ∘ left) (right ∘ right) (H₃₁ c) (ap right (glue (f₃₂ c))) (H₃₃ c))
     ∙ ap (ap to) (! (ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)))
     ∙ (ap (ap to) (! (F₃∙.glue-β c) |in-ctx (ap right))
        ∙ (ap (ap to) (∘-ap right f₃∙ (glue c))
           ∙ ∘-ap to (right ∘ f₃∙) (glue c)
           ∙ ap-∘ i₄∙ f₃∙ (glue c))
        ∙ (F₃∙.glue-β c |in-ctx (ap i₄∙)))
     ∙ ap-∙∙`∘`∘ i₄∙ left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c))
    ∙ (I₄∙.glue-β (f₃₂ c) |in-ctx (λ u → ap (left ∘ right) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))

         =⟨ ap-∘^3-coh to right f₃∙ (glue c) |in-ctx (λ u →
    (! (ap-∙∙`∘`∘ to (right ∘ left) (right ∘ right) (H₃₁ c) (ap right (glue (f₃₂ c))) (H₃₃ c))
     ∙ ap (ap to) (! (ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)))
     ∙ (ap (ap to) (! (F₃∙.glue-β c) |in-ctx (ap right))
        ∙ u
        ∙ (F₃∙.glue-β c |in-ctx (ap i₄∙)))
     ∙ ap-∙∙`∘`∘ i₄∙ left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c))
    ∙ (I₄∙.glue-β (f₃₂ c) |in-ctx (λ u → ap (left ∘ right) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c))))
          ⟩

    (! (ap-∙∙`∘`∘ to (right ∘ left) (right ∘ right) (H₃₁ c) (ap right (glue (f₃₂ c))) (H₃₃ c))
     ∙ ap (ap to) (! (ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)))
     ∙ (ap (ap to) (! (F₃∙.glue-β c) |in-ctx (ap right))
        ∙ ∘-ap to right (ap f₃∙ (glue c))
        ∙ (F₃∙.glue-β c |in-ctx (ap i₄∙)))
     ∙ ap-∙∙`∘`∘ i₄∙ left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c))
    ∙ (I₄∙.glue-β (f₃₂ c) |in-ctx (λ u → ap (left ∘ right) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))

         =⟨ ap-∘-ap-coh to right (F₃∙.glue-β c) |in-ctx (λ u →
    (! (ap-∙∙`∘`∘ to (right ∘ left) (right ∘ right) (H₃₁ c) (ap right (glue (f₃₂ c))) (H₃₃ c))
     ∙ ap (ap to) (! (ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)))
     ∙ u
     ∙ ap-∙∙`∘`∘ i₄∙ left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c))
    ∙ (I₄∙.glue-β (f₃₂ c) |in-ctx (λ u → ap (left ∘ right) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))) ⟩

    (! (ap-∙∙`∘`∘ to (right ∘ left) (right ∘ right) (H₃₁ c) (ap right (glue (f₃₂ c))) (H₃₃ c))
     ∙ ap (ap to) (! (ap-∙∙`∘`∘ right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c)))
     ∙ ∘-ap to right (ap left (H₃₁ c) ∙ glue (f₃₂ c) ∙ ap right (H₃₃ c))
     ∙ ap-∙∙`∘`∘ i₄∙ left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c))
    ∙ (I₄∙.glue-β (f₃₂ c) |in-ctx (λ u → ap (left ∘ right) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))

         =⟨ ap-∘-ap-∙∙3`∘`∘-coh to right left right (H₃₁ c) (glue (f₃₂ c)) (H₃₃ c) |in-ctx (λ u →
                 u ∙ (I₄∙.glue-β (f₃₂ c) |in-ctx (λ u → ap (left ∘ right) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))) ⟩

    (∘-ap to right (glue (f₃₂ c)) |in-ctx (λ u → ap (left ∘ right) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))
    ∙ (I₄∙.glue-β (f₃₂ c) |in-ctx (λ u → ap (left ∘ right) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)))

         =⟨ ∙-|in-ctx (λ u → ap (left ∘ right) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c)) (∘-ap to right (glue (f₃₂ c))) (I₄∙.glue-β (f₃₂ c)) ⟩

    ((∘-ap to right (glue (f₃₂ c)) ∙ I₄∙.glue-β (f₃₂ c)) |in-ctx (λ u → ap (left ∘ right) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c))) ∎

    where

      eq1 : ∀ {i j} {A : Type i} {B : Type j} {f : A → B} {a b c d : A}
        {q : a == b} {r r' : b == c} (e : r == r') {s : c == d}
        {g h k l m n : B} {p : g == f a} {t : f d == h} {u : h == k}
        {v : k == l} {w : l == m} {x : m == n}
         → p ∙ ap f (_ =⟨ q ⟩ _ =⟨ r ⟩ _ =⟨ s ⟩ _ ∎) ∙ t
           ∙ (_ =⟨ u ⟩ _ =⟨ v ⟩ _ =⟨ w ⟩ _ =⟨ x ⟩ _ ∎)
         == (p ∙ ap f q ∙ (ap f r' ∙ (ap f s ∙ t ∙ u) ∙ v) ∙ w) ∙ x
      eq1 {q = idp} {idp} {.idp} idp {idp} {p = p} {idp} {idp} {idp} {idp} {idp} = ! (∙-unit-r (p ∙ idp))

  lemma2'-2 :
    E₂∙Red.rhs-o c
    ∙ ap-∘ to (left ∘ f₁∙) (glue c)
    ∙ ap (ap to) (E∙₂Red.rhs-i c)
    ∙ E∙₂Red.ap-ap-coh!-rhs-i c to
    == (! (∘-ap to left (glue (f₁₂ c)) ∙ I₀∙.glue-β (f₁₂ c)) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c)))
  lemma2'-2 =
    E₂∙Red.rhs-o c ∙ ap-∘ to (left ∘ f₁∙) (glue c) ∙ ap (ap to) (E∙₂Red.rhs-i c) ∙ E∙₂Red.ap-ap-coh!-rhs-i c to

      =⟨ eq1 {f = ap to}
             {p = ! (I₀∙.glue-β (f₁₂ c) |in-ctx (λ u → (ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c))))}
             { ! (ap-∙∙`∘`∘ i₀∙ left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c))}
             { ! (F₁∙.glue-β c |in-ctx ap i₀∙)}
             {∘-ap i₀∙ f₁∙ (glue c)}
             {ap-∘ to (left ∘ f₁∙) (glue c)}
             {ap-∘ left f₁∙ (glue c)}
             {F₁∙.glue-β c |in-ctx (ap left)}
             {ap-∙∙`∘`∘ left left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c)}
             {ap-∙∙`∘`∘ to (left ∘ left) (left ∘ right) (H₁₁ c) (ap left (glue (f₁₂ c))) (H₁₃ c)}
       ⟩

    (! (I₀∙.glue-β (f₁₂ c) |in-ctx (λ u → (ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c)))))
    ∙ ((! (ap-∙∙`∘`∘ i₀∙ left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c)))
       ∙ ((! (F₁∙.glue-β c |in-ctx (λ u → ap i₀∙ u)))
          ∙ (∘-ap i₀∙ f₁∙ (glue c)
             ∙ ap-∘ to (left ∘ f₁∙) (glue c)
             ∙ ap (ap to) (ap-∘ left f₁∙ (glue c)))
          ∙ ap (ap to) (F₁∙.glue-β c |in-ctx (ap left)))
       ∙ ap (ap to) (ap-∙∙`∘`∘ left left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c))
       ∙ ap-∙∙`∘`∘ to (left ∘ left) (left ∘ right) (H₁₁ c) (ap left (glue (f₁₂ c))) (H₁₃ c))

      =⟨ ap-∘^3-coh' to left f₁∙ (glue c)
         |in-ctx (λ u → (! (I₀∙.glue-β (f₁₂ c) |in-ctx (λ u → (ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c)))))
    ∙ ((! (ap-∙∙`∘`∘ i₀∙ left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c)))
       ∙ ((! (F₁∙.glue-β c |in-ctx (λ u → ap i₀∙ u)))
          ∙ u
          ∙ ap (ap to) (F₁∙.glue-β c |in-ctx (ap left)))
       ∙ ap (ap to) (ap-∙∙`∘`∘ left left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c))
       ∙ ap-∙∙`∘`∘ to (left ∘ left) (left ∘ right) (H₁₁ c) (ap left (glue (f₁₂ c))) (H₁₃ c))) ⟩

    (! (I₀∙.glue-β (f₁₂ c) |in-ctx (λ u → (ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c)))))
    ∙ ((! (ap-∙∙`∘`∘ i₀∙ left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c)))
       ∙ ((! (F₁∙.glue-β c |in-ctx (ap i₀∙)))
          ∙ ap-∘ to left (ap f₁∙ (glue c))
          ∙ ap (ap to) (F₁∙.glue-β c |in-ctx (ap left)))
       ∙ ap (ap to) (ap-∙∙`∘`∘ left left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c))
       ∙ ap-∙∙`∘`∘ to (left ∘ left) (left ∘ right) (H₁₁ c) (ap left (glue (f₁₂ c))) (H₁₃ c))

      =⟨ ap-∘-ap-coh'2 to left (F₁∙.glue-β c)
         |in-ctx (λ u → (! (I₀∙.glue-β (f₁₂ c) |in-ctx (λ u → (ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c)))))
    ∙ ((! (ap-∙∙`∘`∘ i₀∙ left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c)))
       ∙ u
       ∙ ap (ap to) (ap-∙∙`∘`∘ left left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c))
       ∙ ap-∙∙`∘`∘ to (left ∘ left) (left ∘ right) (H₁₁ c) (ap left (glue (f₁₂ c))) (H₁₃ c))) ⟩

    (! (I₀∙.glue-β (f₁₂ c) |in-ctx (λ u → (ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c)))))
    ∙ ((! (ap-∙∙`∘`∘ i₀∙ left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c)))
       ∙ ap-∘ to left (ap left (H₁₁ c) ∙ glue (f₁₂ c) ∙ ap right (H₁₃ c))
       ∙ ap (ap to) (ap-∙∙`∘`∘ left left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c))
       ∙ ap-∙∙`∘`∘ to (left ∘ left) (left ∘ right) (H₁₁ c) (ap left (glue (f₁₂ c))) (H₁₃ c))

      =⟨ ap-∘-ap-∙∙2`∘`∘-coh to left left right (H₁₁ c) (glue (f₁₂ c)) (H₁₃ c)
         |in-ctx (λ u → (! (I₀∙.glue-β (f₁₂ c) |in-ctx (λ u → (ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c)))) ∙ u)) ⟩

    (! (I₀∙.glue-β (f₁₂ c) |in-ctx (λ u → (ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c)))))
    ∙ (ap-∘ to left (glue (f₁₂ c)) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c)))

      =⟨ coh2 (glue (f₁₂ c)) (I₀∙.glue-β (f₁₂ c)) ⟩

    (! (∘-ap to left (glue (f₁₂ c)) ∙ I₀∙.glue-β (f₁₂ c)) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c))) ∎

    where

      eq1 : ∀ {i j} {A : Type i} {B : Type j} {f : A → B} {a b c d e : B} {k l m n : A} {o : B}
         {p : a == b} {q : b == c} {r : c == d} {s : d == e} {t : e == f k} {u : k == l}
         {v : l == m} {w : m == n} {x : f n == o}
         → (_ =⟨ p ⟩ _ =⟨ q ⟩ _ =⟨ r ⟩ _ =⟨ s ⟩ _ ∎) ∙ t ∙ ap f (_ =⟨ u ⟩ _ =⟨ v ⟩ _ =⟨ w ⟩ _ ∎) ∙ x
         == (p ∙ (q ∙ ((r ∙ (s ∙ t ∙ ap f u) ∙ ap f v) ∙ ap f w ∙ x)))
      eq1 {p = idp} {idp} {idp} {idp} {t = t} {idp} {idp} {idp} {idp} = ! (∙-unit-r (t ∙ idp)) ∙ ! (∙-unit-r ((t ∙ idp) ∙ idp))

      coh2 : ∀ {i j k l} {A : Type i} {B : Type j} {C : Type k} {D : Type l}
        {a a' : A} (q : a == a') {h : A → B} {g : B → C} {f : (g (h a) == g (h a')) → D} {r : g (h a) == g (h a')} (p : ap (g ∘ h) q == r)
        → (! (p |in-ctx f)) ∙ (ap-∘ g h q |in-ctx f) == (! (∘-ap g h q ∙ p) |in-ctx f)
      coh2 idp idp = idp

  lemma2-4' =
    ap□ to (↓-='-out (apd (glue {d = v-h-span}) (glue c))
              ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /)
    ∙□-i/ E∙₂Red.ap-ap-coh!-lhs-i c to / E∙₂Red.ap-ap-coh!-rhs-i c to /

         =⟨ lemma2-5 |in-ctx (λ u → u ∙□-i/ E∙₂Red.ap-ap-coh!-lhs-i c to / E∙₂Red.ap-ap-coh!-rhs-i c to /) ⟩

    E₂∙Red.coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                  ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /)
    ∙□-i/ E₂∙Red.lhs-o c / E₂∙Red.rhs-o c /
    ∙□-o/ To.glue-β (left (f₂₁ c)) / ! (To.glue-β (right (f₂₃ c))) /
    ∙□-i/ ∘-ap to (right ∘ f₃∙) (glue c) / ap-∘ to (left ∘ f₁∙) (glue c) /
    ∙□-i/ ap (ap to) (E∙₂Red.lhs-i c) / ap (ap to) (E∙₂Red.rhs-i c) /
    ∙□-i/ E∙₂Red.ap-ap-coh!-lhs-i c to / E∙₂Red.ap-ap-coh!-rhs-i c to /

         =⟨ assoc (E₂∙Red.coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                   ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /))
                   (E₂∙Red.lhs-o c) (∘-ap to (right ∘ f₃∙) (glue c)) (ap (ap to) (E∙₂Red.lhs-i c))
                   (E∙₂Red.ap-ap-coh!-lhs-i c to) _ _ _ _ (To.glue-β (left (f₂₁ c))) _ ⟩

    E₂∙Red.coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                   ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /)
    ∙□-o/ To.glue-β (left (f₂₁ c)) / ! (To.glue-β (right (f₂₃ c))) /
    ∙□-i/ E∙₂Red.ap-ap-coh!-lhs-i c to ∙ ap (ap to) (E∙₂Red.lhs-i c) ∙ ∘-ap to (right ∘ f₃∙) (glue c) ∙ E₂∙Red.lhs-o c
        / E₂∙Red.rhs-o c ∙ ap-∘ to (left ∘ f₁∙) (glue c) ∙ ap (ap to) (E∙₂Red.rhs-i c) ∙ E∙₂Red.ap-ap-coh!-rhs-i c to /

         =⟨ ∙□-i/-rewrite (E₂∙Red.coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                   ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /)
    ∙□-o/ To.glue-β (left (f₂₁ c)) / ! (To.glue-β (right (f₂₃ c))) /) lemma2'-1 lemma2'-2 ⟩

    E₂∙Red.coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                   ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /)
    ∙□-o/ To.glue-β (left (f₂₁ c)) / ! (To.glue-β (right (f₂₃ c))) /
    ∙□-i/ (∘-ap to right (glue (f₃₂ c)) ∙ I₄∙.glue-β (f₃₂ c)) |in-ctx (λ u → ap (left ∘ right) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c))
        / (! (∘-ap to left (glue (f₁₂ c)) ∙ I₀∙.glue-β (f₁₂ c))) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c)) / ∎  where

      assoc : ∀ {i} {A : Type i} {a b b' c : A} {u u' : a == b} {v v1 v2 v3 v4 : b == c}
         {w w1 w2 w3 w4 : a == b'} {x x' : b' == c} (α : (u , v =□ w , x))
         (p1 : v1 == v) (p2 : v2 == v1) (p3 : v3 == v2) (p4 : v4 == v3)
         (q1 : w == w1) (q2 : w1 == w2) (q3 : w2 == w3) (q4 : w3 == w4)
         (r : u' == u) (s : x == x')
         → α ∙□-i/ p1 / q1 / ∙□-o/ r / s / ∙□-i/ p2 / q2 / ∙□-i/ p3 / q3 / ∙□-i/ p4 / q4 /
         == α ∙□-o/ r / s / ∙□-i/ p4 ∙ p3 ∙ p2 ∙ p1 / q1 ∙ q2 ∙ q3 ∙ q4 /
      assoc α idp idp idp idp idp idp idp idp idp idp = idp

  lemma2-4'' =
    E∙₂Red.ap-ap-coh! c to (ap□ to (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                                       ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /)
                             ∙□-i/ E∙₂Red.ap-ap-coh!-lhs-i c to / E∙₂Red.ap-ap-coh!-rhs-i c to /)

         =⟨ lemma2-4' |in-ctx (E∙₂Red.ap-ap-coh! c to) ⟩

    E∙₂Red.ap-ap-coh! c to (E₂∙Red.coh c (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                                            ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /)
                             ∙□-o/ To.glue-β (left (f₂₁ c)) / ! (To.glue-β (right (f₂₃ c))) /
                             ∙□-i/ (∘-ap to right (glue (f₃₂ c)) ∙ I₄∙.glue-β (f₃₂ c)) |in-ctx (λ u → ap (left ∘ right) (H₃₁ c) ∙ u ∙ ap (right ∘ right) (H₃₃ c))
                                 / (! (∘-ap to left (glue (f₁₂ c)) ∙ I₀∙.glue-β (f₁₂ c))) |in-ctx (λ u → ap (left ∘ left) (H₁₁ c) ∙ u ∙ ap (right ∘ left) (H₁₃ c))/)

         =⟨ lemma! (∘-ap to left (glue (f₁₂ c)) ∙ I₀∙.glue-β (f₁₂ c)) (To.glue-β (right (f₂₃ c))) (To.glue-β (left (f₂₁ c))) (∘-ap to right (glue (f₃₂ c)) ∙ I₄∙.glue-β (f₃₂ c))
                   (↓-='-out (apd (glue {d = h-v-span}) (glue c))
                   ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /) ⟩

    ↓-='-out (apd (glue {d = h-v-span}) (glue c))
    ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /
    ∙□-o/ ∘-ap to left (glue (f₁₂ c)) ∙ I₀∙.glue-β (f₁₂ c) / ! (∘-ap to right (glue (f₃₂ c)) ∙ I₄∙.glue-β (f₃₂ c)) /
    ∙□-i/ (To.glue-β (right (f₂₃ c))) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c)))
        / (! (To.glue-β (left (f₂₁ c)))) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (left ∘ right) (H₃₁ c)) / ∎

  lemma2-4 =
    ap□ to (E∙₂Red.coh! c (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                            ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /))

         =⟨ E∙₂Red.ap-ap-coh!-β c to (↓-='-out (apd (glue {d = v-h-span}) (glue c)) ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /) ⟩

    E∙₂Red.ap-ap-coh! c to (ap□ to (↓-='-out (apd (glue {d = v-h-span}) (glue c))
                                       ∙□-i/ E∙₂Red.lhs-i c / E∙₂Red.rhs-i c /)
                             ∙□-i/ E∙₂Red.ap-ap-coh!-lhs-i c to / E∙₂Red.ap-ap-coh!-rhs-i c to /)
    ∙□-i/ E∙₂Red.ap-ap-coh!-lhs-o c to / E∙₂Red.ap-ap-coh!-rhs-o c to /

         =⟨ lemma2-4'' |in-ctx (λ u → u ∙□-i/ E∙₂Red.ap-ap-coh!-lhs-o c to / E∙₂Red.ap-ap-coh!-rhs-o c to /) ⟩

    ↓-='-out (apd (glue {d = h-v-span}) (glue c))
    ∙□-i/ E₂∙Red.lhs-i c / E₂∙Red.rhs-i c /
    ∙□-o/ ∘-ap to left (glue (f₁₂ c)) ∙ I₀∙.glue-β (f₁₂ c) / ! (∘-ap to right (glue (f₃₂ c)) ∙ I₄∙.glue-β (f₃₂ c)) /
    ∙□-i/ (To.glue-β (right (f₂₃ c))) |in-ctx (λ u → ap (right ∘ left) (H₁₃ c) ∙ u ∙ ! (ap (right ∘ right) (H₃₃ c)))
        / (! (To.glue-β (left (f₂₁ c)))) |in-ctx (λ u → ! (ap (left ∘ left) (H₁₁ c)) ∙ u ∙ ap (left ∘ right) (H₃₁ c)) /
    ∙□-i/ E∙₂Red.ap-ap-coh!-lhs-o c to / E∙₂Red.ap-ap-coh!-rhs-o c to / ∎
