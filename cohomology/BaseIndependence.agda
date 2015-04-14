{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.FunctionOver
open import cohomology.Theory

{- Cohomology groups are independent of basepoint, and the action of
 - the cohomology is independent of the basepoint-preservation path -}

module cohomology.BaseIndependence {i} (CT : CohomologyTheory i) where

open CohomologyTheory CT

C-base-indep : (n : ℤ) {A : Type i} (a₀ a₁ : A)
  → C n (A , a₀) ≃ᴳ C n (A , a₁)
C-base-indep n a₀ a₁ =
  C-Susp n (_ , a₁) ∘eᴳ (C-Susp n (_ , a₀))⁻¹ᴳ

CF-base-indep : (n : ℤ) {X Y : Ptd i}
  (f : fst X → fst Y) (p₁ p₂ : f (snd X) == snd Y)
  → CF-hom n (f , p₁) == CF-hom n (f , p₂)
CF-base-indep n {X} {Y} f p₁ p₂ = transport
  (λ q → CF-hom n (f , p₁) == CF-hom n (f , p₂) [ uncurry _→ᴳ_ ↓ q ])
  (!-inv-l (pair×= (group-ua (C-Susp n Y)) (group-ua (C-Susp n X))))
  (!ᵈ (C-Susp-↓ n (f , p₁)) ∙ᵈ C-Susp-↓ n (f , p₂))

CF-λ= : (n : ℤ) {X Y : Ptd i} {f g : fst (X ⊙→ Y)}
  → (∀ x → fst f x == fst g x)
  → CF-hom n f == CF-hom n g
CF-λ= n h = CF-base-indep n _ _ _ ∙ ap (CF-hom n) (⊙λ= h idp)

CF-↓dom= : (n : ℤ) {X Y Z : Ptd i}
  {f : fst (X ⊙→ Y)} {g : fst (X ⊙→ Z)} {p : Y == Z}
  → fst f == fst g [ (λ V → fst X → fst V) ↓ p ]
  → CF-hom n f == CF-hom n g [ (λ G → G →ᴳ C n X) ↓ ap (C n) p ]
CF-↓dom= n {p = idp} r =
  CF-base-indep n _ _ _ ∙ ap (CF-hom n) (pair= r (from-transp! _ _ idp))

CF-↓cod= : (n : ℤ) {X Y Z : Ptd i}
  {f : fst (X ⊙→ Z)} {g : fst (Y ⊙→ Z)} {p : X == Y}
  → fst f == fst g [ (λ U → fst U → fst Z) ↓ p ]
  → CF-hom n f == CF-hom n g [ (λ G → C n Z →ᴳ G) ↓ ap (C n) p ]
CF-↓cod= n {p = idp} r =
  CF-base-indep n _ _ _ ∙ ap (CF-hom n) (pair= r (from-transp! _ _ idp))
