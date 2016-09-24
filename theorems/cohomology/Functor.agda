{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.FunctionOver
open import cohomology.Theory

{- Useful lemmas concerning the functorial action of C -}

module cohomology.Functor {i} (CT : CohomologyTheory i) where

open CohomologyTheory CT

open import cohomology.Unit CT
open import cohomology.BaseIndependence CT

CF-cst : (n : ℤ) {X Y : Ptd i} → CF-hom n (⊙cst {X = X} {Y = Y}) == cst-hom
CF-cst n {X} {Y} =
  CF-hom n (⊙cst {X = ⊙LU} ⊙∘ ⊙cst {X = X})
    =⟨ CF-comp n ⊙cst ⊙cst ⟩
  (CF-hom n (⊙cst {X = X})) ∘ᴳ (CF-hom n (⊙cst {X = ⊙LU}))
    =⟨ group-hom= {φ = CF-hom n (⊙cst {X = ⊙LU})} {ψ = cst-hom}
            (contr-has-all-paths (→-level (C-Unit-is-contr n)) _ _)
       |in-ctx (λ w → CF-hom n (⊙cst {X = X} {Y = ⊙LU}) ∘ᴳ w) ⟩
  (CF-hom n (⊙cst {X = X} {Y = ⊙LU})) ∘ᴳ cst-hom
    =⟨ pre∘-cst-hom (CF-hom n (⊙cst {X = X} {Y = ⊙LU})) ⟩
  cst-hom ∎
  where
  ⊙LU = ⊙Lift {j = i} ⊙Unit

CF-inverse : (n : ℤ) {X Y : Ptd i} (f : X ⊙→ Y) (g : Y ⊙→ X)
  → (∀ x → fst g (fst f x) == x)
  → (CF-hom n f) ∘ᴳ (CF-hom n g) == idhom _
CF-inverse n f g p = ! (CF-comp n g f) ∙ CF-λ= n p ∙ CF-ident n

CF-iso : (n : ℤ) {X Y : Ptd i} → X ⊙≃ Y → C n Y ≃ᴳ C n X
CF-iso n (f , ie) =
  (CF-hom n f ,
   is-eq _ (GroupHom.f (CF-hom n (⊙<– (f , ie))))
     (app= $ ap GroupHom.f $ CF-inverse n f _ $ <–-inv-l (fst f , ie))
     (app= $ ap GroupHom.f $ CF-inverse n _ f $ <–-inv-r (fst f , ie)))
