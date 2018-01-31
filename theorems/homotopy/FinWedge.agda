{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.FinWedge where

module _ {i} {I} (X : Fin I → Ptd i) where

  {- the function for cofiber -}
  finwedge-f : Fin I → Σ (Fin I) (de⊙ ∘ X)
  finwedge-f = bigwedge-f X

  FinWedge : Type i
  FinWedge = BigWedge X

  ⊙FinWedge : Ptd i
  ⊙FinWedge = ⊙BigWedge X

module _ {i} {I} {X : Fin I → Ptd i} where

  fwbase : FinWedge X
  fwbase = bwbase

  fwin : (<I : Fin I) → de⊙ (X <I) → FinWedge X
  fwin = bwin

  ⊙fwin : (<I : Fin I) → X <I ⊙→ ⊙FinWedge X
  ⊙fwin = ⊙bwin

  fwglue : (<I : Fin I) → fwbase == fwin <I (pt (X <I))
  fwglue = cfglue

module _ {i} {I} {X : Ptd i} where

  ⊙fwproj-in : Fin I → Fin I → X ⊙→ X
  ⊙fwproj-in = ⊙bwproj-in Fin-has-dec-eq

  module FinWedgeProj (<I : Fin I) = BigWedgeProj Fin-has-dec-eq {X = X} <I

  fwproj : Fin I → FinWedge (λ _ → X) → de⊙ X
  fwproj = FinWedgeProj.f

  ⊙fwproj : Fin I → ⊙FinWedge (λ _ → X) ⊙→ X
  ⊙fwproj <I = fwproj <I , idp

  fwproj-fwin-diag : (<I : Fin I) → fwproj <I ∘ fwin <I ∼ idf (de⊙ X)
  fwproj-fwin-diag <I = bwproj-bwin-diag Fin-has-dec-eq <I

  fwproj-fwin-≠ : ∀ {<I <I'} → <I ≠ <I' → fwproj <I ∘ fwin <I' ∼ cst (pt X)
  fwproj-fwin-≠ = bwproj-bwin-≠ Fin-has-dec-eq

module _ {i₀ i₁} {I} {X₀ : Fin I → Ptd i₀} {X₁ : Fin I → Ptd i₁}
  (Xeq : ∀ <I → X₀ <I ⊙≃ X₁ <I) where

  finwedge-span-emap-r : SpanEquiv (cofiber-span (finwedge-f X₀)) (cofiber-span (finwedge-f X₁))
  finwedge-span-emap-r = bigwedge-span-emap-r Xeq

  FinWedge-emap-r : FinWedge X₀ ≃ FinWedge X₁
  FinWedge-emap-r = BigWedge-emap-r Xeq

  ⊙FinWedge-emap-r : ⊙FinWedge X₀ ⊙≃ ⊙FinWedge X₁
  ⊙FinWedge-emap-r = ⊙BigWedge-emap-r Xeq

module _ {i j} {I} {X : Ptd i} (<I : Fin I) where
  abstract
    fwproj-FinWedge-emap-r-lift :
        fwproj {X = ⊙Lift {j = j} X} <I ∘ –> (FinWedge-emap-r (λ _ → ⊙lift-equiv {j = j}))
      ∼ lift {j = j} ∘ fwproj {X = X} <I
    fwproj-FinWedge-emap-r-lift = bwproj-BigWedge-emap-r-lift Fin-has-dec-eq <I
