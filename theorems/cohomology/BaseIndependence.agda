{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory

{- Cohomology groups are independent of basepoint, and the action of
 - the cohomology is independent of the basepoint-preservation path -}

module cohomology.BaseIndependence {i} (CT : CohomologyTheory i) where

open CohomologyTheory CT

C-base-indep : (n : ℤ) {A : Type i} (a₀ a₁ : A)
  → C n ⊙[ A , a₀ ] ≃ᴳ C n ⊙[ A , a₁ ]
C-base-indep n a₀ a₁ =
  C-Susp n ⊙[ _ , a₁ ] ∘eᴳ (C-Susp n ⊙[ _ , a₀ ])⁻¹ᴳ

CEl-fmap-base-indep : (n : ℤ) {X Y : Ptd i}
  (f : de⊙ X → de⊙ Y) (p₁ p₂ : f (pt X) == pt Y)
  → ∀ y → CEl-fmap n (f , p₁) y == CEl-fmap n (f , p₂) y
CEl-fmap-base-indep n {X} {Y} f p₁ p₂ y =
  CEl-fmap n (f , p₁) y
    =⟨ ! $ <–-inv-r (CEl-Susp n Y) y |in-ctx CEl-fmap n (f , p₁) ⟩
  CEl-fmap n (f , p₁) (–> (CEl-Susp n Y) (<– (CEl-Susp n Y) y))
    =⟨ ! $ commutes (CEl-Susp-fmap n (f , p₁)) (<– (CEl-Susp n Y) y) ⟩
  –> (CEl-Susp n X) (CEl-fmap (succ n) (Susp-fmap f , idp) (<– (CEl-Susp n Y) y))
    =⟨ commutes (CEl-Susp-fmap n (f , p₂)) (<– (CEl-Susp n Y) y) ⟩
  CEl-fmap n (f , p₂) (–> (CEl-Susp n Y) (<– (CEl-Susp n Y) y))
    =⟨ <–-inv-r (CEl-Susp n Y) y |in-ctx CEl-fmap n (f , p₂) ⟩
  CEl-fmap n (f , p₂) y
    =∎

C-fmap-base-indep = CEl-fmap-base-indep

-- FIXME is there a better name?
CEl-fmap-base-indep' : (n : ℤ) {X Y : Ptd i} {f g : X ⊙→ Y}
  → (∀ x → fst f x == fst g x)
  → (∀ y → CEl-fmap n f y == CEl-fmap n g y)
CEl-fmap-base-indep' n h y = CEl-fmap-base-indep n _ _ _ _
                           ∙ ap (λ f → CEl-fmap n f y) (⊙λ= h (↓-idf=cst-in' idp))

C-fmap-base-indep' = CEl-fmap-base-indep'

{-
CF-↓dom= : (n : ℤ) {X Y Z : Ptd i}
  {f : X ⊙→ Y} {g : X ⊙→ Z} {p : Y == Z}
  → fst f == fst g [ (λ V → de⊙ X → fst V) ↓ p ]
  → CF-hom n f == CF-hom n g [ (λ G → G →ᴳ C n X) ↓ ap (C n) p ]
CF-↓dom= n {p = idp} r =
  CF-base-indep n _ _ _ ∙ ap (CF-hom n) (pair= r (from-transp! _ _ idp))

CF-↓cod= : (n : ℤ) {X Y Z : Ptd i}
  {f : X ⊙→ Z} {g : Y ⊙→ Z} {p : X == Y}
  → fst f == fst g [ (λ U → fst U → de⊙ Z) ↓ p ]
  → CF-hom n f == CF-hom n g [ (λ G → C n Z →ᴳ G) ↓ ap (C n) p ]
CF-↓cod= n {p = idp} r =
  CF-base-indep n _ _ _ ∙ ap (CF-hom n) (pair= r (from-transp! _ _ idp))
-}
