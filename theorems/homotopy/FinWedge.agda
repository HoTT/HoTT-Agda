{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.FinWedge where

module _ {i} {I} (X : Fin I → Ptd i) where

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

  fwproj-basis-diag : ∀ <I → fwproj-basis <I <I == ⊙idf _
  fwproj-basis-diag <I = Fin-basis-diag (λ <I' → ⊙[ X <I' ⊙→ X <I , ⊙cst ]) <I (⊙idf _)

  fwproj-fwin-diag : ∀ <I → fwproj <I ∘ fwin <I ∼ idf _
  fwproj-fwin-diag <I x = ap (λ f → fst f x) (fwproj-basis-diag <I)
  
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
