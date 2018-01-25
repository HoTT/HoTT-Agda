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

  fwproj-basis : ∀ <I → ∀ <I' → (X <I' ⊙→ X <I)
  fwproj-basis <I = Fin-basis (λ <I' → ⊙[ X <I' ⊙→ X <I , ⊙cst ]) <I (⊙idf _)

  module FinWedgeProj (<I : Fin I)
    = BigWedgeRec (pt (X <I))
        (fst ∘ fwproj-basis <I)
        (! ∘ snd ∘ fwproj-basis <I)

  fwproj : ∀ <I → FinWedge X → de⊙ (X <I)
  fwproj = FinWedgeProj.f

  ⊙fwproj : ∀ <I → ⊙FinWedge X ⊙→ X <I
  ⊙fwproj <I = fwproj <I , idp

  fwproj-fwin-diag : ∀ <I → fwproj <I ∘ fwin <I ∼ idf _
  fwproj-fwin-diag <I x = ap (λ f → fst f x)
    (Fin-basis-diag (λ <I' → ⊙[ X <I' ⊙→ X <I , ⊙cst ]) <I (⊙idf _))
  
module _ {i} n {I} {X : Fin (ℕ-S^' (S n) I) → Ptd i} where

  fwproj-fwin-early : ∀ <I
    → fwproj {X = X} (Fin-S^' (S n) <I) ∘ fwin {X = X} (Fin-S^' n (I , ltS))
    ∼ cst (pt (X (Fin-S^' (S n) <I)))
  fwproj-fwin-early <I x = ap (λ f → fst f x)
    (Fin-basis-late n (λ <I' → ⊙[ X <I' ⊙→ X (Fin-S^' (S n) <I) , ⊙cst ]) <I (⊙idf _))

  fwproj-fwin-late : ∀ <I
    → fwproj {X = X} (Fin-S^' n (I , ltS)) ∘ fwin {X = X} (Fin-S^' (S n) <I)
    ∼ cst (pt (X (Fin-S^' n (I , ltS))))
  fwproj-fwin-late <I x = ap (λ f → fst f x)
    (Fin-basis-early n (λ <I' → ⊙[ X <I' ⊙→ X (Fin-S^' n (I , ltS)) , ⊙cst ]) <I (⊙idf _))

module _ {i₀ i₁} {I} {X₀ : Fin I → Ptd i₀} {X₁ : Fin I → Ptd i₁}
  (Xeq : ∀ <I → X₀ <I ⊙≃ X₁ <I) where

  finwedge-span-emap-r : SpanEquiv (cofiber-span (finwedge-f X₀)) (cofiber-span (finwedge-f X₁))
  finwedge-span-emap-r = bigwedge-span-emap-r Xeq

  FinWedge-emap-r : FinWedge X₀ ≃ FinWedge X₁
  FinWedge-emap-r = BigWedge-emap-r Xeq

  ⊙FinWedge-emap-r : ⊙FinWedge X₀ ⊙≃ ⊙FinWedge X₁
  ⊙FinWedge-emap-r = ⊙BigWedge-emap-r Xeq

module _ {i j} {I} {X : Fin I → Ptd i} where

  postulate {- TODO -}
    fwproj-FinWedge-emap-r-lift : ∀ (<I : Fin I)
      → fwproj {X = ⊙Lift {j = j} ∘ X} <I ∘ fst (FinWedge-emap-r (λ _ → ⊙lift-equiv {j = j}))
      ∼ lift {j = j} ∘ fwproj {X = X} <I
