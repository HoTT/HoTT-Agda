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

  module _ (<I : Fin I) where

    ⊙fwproj-in : ∀ <I' → (X <I' ⊙→ X <I)
    ⊙fwproj-in = Fin-basis (λ <I' → ⊙[ X <I' ⊙→ X <I , ⊙cst ]) <I (⊙idf _)

    module FinWedgeProj = BigWedgeRec
      (pt (X <I)) (fst ∘ ⊙fwproj-in)
      (! ∘ snd ∘ ⊙fwproj-in)

    fwproj : FinWedge X → de⊙ (X <I)
    fwproj = FinWedgeProj.f

    ⊙fwproj : ⊙FinWedge X ⊙→ X <I
    ⊙fwproj = fwproj , idp

    fwproj-fwin-diag : fwproj ∘ fwin <I ∼ idf _
    fwproj-fwin-diag x = ap (λ f → fst f x)
      (Fin-basis-diag (λ <I' → ⊙[ X <I' ⊙→ X <I , ⊙cst ]) <I (⊙idf _))

    fwproj-fwin-≠ : ∀ {<J} → <I ≠ <J → fwproj ∘ fwin <J ∼ cst (pt (X <I))
    fwproj-fwin-≠ neq x = ap (λ f → fst f x)
      (Fin-basis-≠ (λ <I' → ⊙[ X <I' ⊙→ X <I , ⊙cst ]) <I (⊙idf _) neq)

    ⊙fwproj-in-is-⊙bwproj-in : ⊙fwproj-in ∼ ⊙bwproj-in Fin-has-dec-eq X <I
    ⊙fwproj-in-is-⊙bwproj-in <I' with Fin-has-dec-eq <I <I'
    ... | inl idp = Fin-basis-diag (λ <I' → ⊙[ X <I' ⊙→ X <I , ⊙cst ]) <I (⊙idf _)
    ... | inr neq = Fin-basis-≠ (λ <I' → ⊙[ X <I' ⊙→ X <I , ⊙cst ]) <I (⊙idf _) neq

    fwproj-is-bwproj : fwproj ∼ bwproj Fin-has-dec-eq X <I
    fwproj-is-bwproj x =
      ap (λ ⊙in → BigWedgeRec.f (pt (X <I)) (fst ∘ ⊙in) (! ∘ snd ∘ ⊙in) x)
        (λ= ⊙fwproj-in-is-⊙bwproj-in)

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

module _ {i j} where

  private
    fwproj-FinWedge-emap-r-lift-in :
      ∀ {I} {X : Fin I → Ptd i} (<I <I' : Fin I) x
      →  fwproj {X = ⊙Lift {j = j} ∘ X} <I (fwin <I' (lift x))
      == lift {j = j} (fwproj {X = X} <I (fwin <I' x))
    fwproj-FinWedge-emap-r-lift-in (_ , ltS) (_ , ltS) x = idp
    fwproj-FinWedge-emap-r-lift-in (_ , ltSR lt₀) (_ , ltSR lt₁) x =
      fwproj-FinWedge-emap-r-lift-in (_ , lt₀) (_ , lt₁) x
    fwproj-FinWedge-emap-r-lift-in (_ , ltS) (_ , ltSR _) x = idp
    fwproj-FinWedge-emap-r-lift-in (_ , ltSR _) (_ , ltS) x = idp

    fwproj-FinWedge-emap-r-lift-glue' :
      ∀ {I} {X : Fin I → Ptd i} (<I <I' : Fin I)
      → ap (lift {j = j}) (! (snd (⊙fwproj-in {X = X} <I <I')))
      == ! (snd (⊙fwproj-in <I <I')) ∙' fwproj-FinWedge-emap-r-lift-in <I <I' (pt (X <I'))
    fwproj-FinWedge-emap-r-lift-glue' (_ , ltS) (_ , ltS) = idp
    fwproj-FinWedge-emap-r-lift-glue' (_ , ltSR lt₀) (_ , ltSR lt₁) =
      fwproj-FinWedge-emap-r-lift-glue' (_ , lt₀) (_ , lt₁)
    fwproj-FinWedge-emap-r-lift-glue' (_ , ltS) (_ , ltSR _) = idp
    fwproj-FinWedge-emap-r-lift-glue' (_ , ltSR _) (_ , ltS) = idp

    fwproj-FinWedge-emap-r-lift-glue :
      ∀ {I} {X : Fin I → Ptd i} (<I <I' : Fin I)
      →  idp
      == fwproj-FinWedge-emap-r-lift-in {I = I} {X = X} <I <I' (pt (X <I'))
      [ (λ x → fwproj {X = ⊙Lift {j = j} ∘ X} <I (–> (FinWedge-emap-r (λ _ → ⊙lift-equiv {j = j})) x)
            == lift {j = j} (fwproj {X = X} <I x)) ↓ fwglue <I' ]
    fwproj-FinWedge-emap-r-lift-glue {I} {X} <I <I' = ↓-='-in' $
      ap (lift {j = j} ∘ fwproj {X = X} <I) (fwglue <I')
        =⟨ ap-∘ (lift {j = j}) (fwproj {X = X} <I) (fwglue <I') ⟩
      ap (lift {j = j}) (ap (fwproj {X = X} <I) (fwglue <I'))
        =⟨ ap (ap (lift {j = j})) $ FinWedgeProj.glue-β <I <I' ⟩
      ap (lift {j = j}) (! (snd (⊙fwproj-in <I <I')))
        =⟨ fwproj-FinWedge-emap-r-lift-glue' {X = X} <I <I' ⟩
      ! (snd (⊙fwproj-in <I <I')) ∙' fwproj-FinWedge-emap-r-lift-in <I <I' (pt (X <I'))
        =⟨ ap (_∙' fwproj-FinWedge-emap-r-lift-in <I <I' (pt (X <I'))) $
            ( ! $ FinWedgeProj.glue-β <I <I') ⟩
      ap (fwproj {X = ⊙Lift {j = j} ∘ X} <I) (fwglue <I')
      ∙' fwproj-FinWedge-emap-r-lift-in <I <I' (pt (X <I'))
        =⟨ ap (λ p → ap (fwproj {X = ⊙Lift {j = j} ∘ X} <I) p
                  ∙' fwproj-FinWedge-emap-r-lift-in <I <I' (pt (X <I'))) $
            (! $ PushoutFmap.glue-β (fst (bigwedge-span-emap-r (λ _ → ⊙lift-equiv {j = j}))) <I') ⟩
      ap (fwproj {X = ⊙Lift {j = j} ∘ X} <I) (ap (–> (FinWedge-emap-r (λ _ → ⊙lift-equiv {j = j}))) (fwglue <I'))
      ∙' fwproj-FinWedge-emap-r-lift-in <I <I' (pt (X <I'))
        =⟨ ap (_∙' fwproj-FinWedge-emap-r-lift-in <I <I' (pt (X <I'))) $
            (∘-ap (fwproj {X = ⊙Lift {j = j} ∘ X} <I) (–> (FinWedge-emap-r (λ _ → ⊙lift-equiv {j = j}))) (fwglue <I')) ⟩
      ap (fwproj {X = ⊙Lift {j = j} ∘ X} <I ∘ –> (FinWedge-emap-r (λ _ → ⊙lift-equiv {j = j}))) (fwglue <I')
      ∙' fwproj-FinWedge-emap-r-lift-in <I <I' (pt (X <I'))
        =∎

  abstract
    fwproj-FinWedge-emap-r-lift :
      ∀ {I} {X : Fin I → Ptd i} (<I : Fin I)
      → fwproj {X = ⊙Lift {j = j} ∘ X} <I ∘ –> (FinWedge-emap-r (λ _ → ⊙lift-equiv {j = j}))
      ∼ lift {j = j} ∘ fwproj {X = X} <I
    fwproj-FinWedge-emap-r-lift <I =
      BigWedge-elim idp
        (fwproj-FinWedge-emap-r-lift-in <I)
        (fwproj-FinWedge-emap-r-lift-glue <I)
