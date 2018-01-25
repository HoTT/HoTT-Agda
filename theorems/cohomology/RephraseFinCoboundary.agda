{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.FinWedge
open import homotopy.Bouquet
open import groups.FinProduct 
open import groups.SphereEndomorphism
open import cohomology.Theory

module cohomology.RephraseFinCoboundary (CT : CohomologyTheory lzero) (n : ℤ) (m : ℕ) where

open CohomologyTheory CT
open import cohomology.FinWedge CT n
open import cohomology.SphereEndomorphism CT n m

abstract
  rephrase-in-degrees₀ : ∀ {I J : ℕ} (f : ⊙FinBouquetLift I (S m) ⊙→ ⊙FinBouquetLift J (S m)) g
    → CEl-finite-additive (FinBouquetLift-family I (S m))
        (CEl-fmap n f (is-equiv.g (C-finite-additive-is-equiv (FinBouquetLift-family J (S m))) g))
    ∼ λ <I → Group.sum (C n (⊙Lift (⊙Sphere (S m))))
          (λ <J → Group.exp (C n (⊙Lift (⊙Sphere (S m)))) (g <J) (⊙LiftSphereS-endo-degree m (⊙fwproj <J ⊙∘ f ⊙∘ ⊙fwin <I)))
  rephrase-in-degrees₀ {I} {J} f g <I =
    CEl-fmap n (⊙fwin <I)
      (CEl-fmap n f
        (is-equiv.g (C-finite-additive-is-equiv (FinBouquetLift-family J (S m))) g))
      =⟨ ap ( CEl-fmap n (⊙fwin <I)
            ∘ CEl-fmap n f
            ∘ is-equiv.g (C-finite-additive-is-equiv (FinBouquetLift-family J (S m)))) $
          (Πᴳ-η (λ _ → C n (⊙Lift (⊙Sphere (S m)))) g) ⟩
    CEl-fmap n (⊙fwin <I)
      (CEl-fmap n f
        (is-equiv.g (C-finite-additive-is-equiv (FinBouquetLift-family J (S m)))
          (Group.sum (Πᴳ _ (λ _ → C n (⊙Lift (⊙Sphere (S m))))) (λ <J →
            Πᴳ-basis (λ _ → C n (⊙Lift (⊙Sphere (S m)))) <J (g <J)))))
      =⟨ ap (CEl-fmap n (⊙fwin <I) ∘ CEl-fmap n f) $
          GroupHom.pres-sum (GroupIso.g-hom (C-finite-additive-iso (FinBouquetLift-family J (S m))))
            (λ <J → Πᴳ-basis (λ _ → C n (⊙Lift (⊙Sphere (S m)))) <J (g <J)) ⟩
    CEl-fmap n (⊙fwin <I)
      (CEl-fmap n f
        (Group.sum (C n (⊙FinBouquetLift J (S m))) (λ <J →
          is-equiv.g (C-finite-additive-is-equiv (FinBouquetLift-family J (S m)))
            (Πᴳ-basis (λ _ → C n (⊙Lift (⊙Sphere (S m)))) <J (g <J)))))
      =⟨ ap ( CEl-fmap n (⊙fwin <I)
            ∘ CEl-fmap n f
            ∘ Group.sum (C n (⊙FinBouquetLift J (S m))))
          (λ= λ <J → inverse-C-finite-additive-basis' (FinBouquetLift-family J (S m)) <J (g <J)) ⟩
    CEl-fmap n (⊙fwin <I)
      (CEl-fmap n f
        (Group.sum (C n (⊙FinBouquetLift J (S m))) (λ <J →
          CEl-fmap n (⊙fwproj <J) (g <J))))
      =⟨ ap (CEl-fmap n (⊙fwin <I)) $
          GroupHom.pres-sum (C-fmap n f) (λ <J →
            CEl-fmap n (⊙fwproj <J) (g <J)) ⟩
    CEl-fmap n (⊙fwin <I)
      (Group.sum (C n (⊙FinBouquetLift I (S m))) (λ <J →
        CEl-fmap n f
          (CEl-fmap n (⊙fwproj <J) (g <J))))
      =⟨ GroupHom.pres-sum (C-fmap n (⊙fwin <I)) (λ <J →
          CEl-fmap n f
            (CEl-fmap n (⊙fwproj <J) (g <J))) ⟩
    Group.sum (C n (⊙Lift (⊙Sphere (S m)))) (λ <J →
      CEl-fmap n (⊙fwin <I)
        (CEl-fmap n f
          (CEl-fmap n (⊙fwproj <J) (g <J))))
      =⟨ ap (Group.sum (C n (⊙Lift (⊙Sphere (S m)))))
          (λ= λ <J → ∘-CEl-fmap n (⊙fwin <I) f (CEl-fmap n (⊙fwproj <J) (g <J))) ⟩
    Group.sum (C n (⊙Lift (⊙Sphere (S m)))) (λ <J →
      CEl-fmap n (f ⊙∘ ⊙fwin <I)
        (CEl-fmap n (⊙fwproj <J) (g <J)))
      =⟨ ap (Group.sum (C n (⊙Lift (⊙Sphere (S m)))))
          (λ= λ <J → ∘-CEl-fmap n (f ⊙∘ ⊙fwin <I) (⊙fwproj <J) (g <J)) ⟩
    Group.sum (C n (⊙Lift (⊙Sphere (S m)))) (λ <J →
      CEl-fmap n (⊙fwproj <J ⊙∘ f ⊙∘ ⊙fwin <I) (g <J))
      =⟨ ap (Group.sum (C n (⊙Lift (⊙Sphere (S m)))))
          (λ= λ <J → CEl-fmap-η (⊙fwproj <J ⊙∘ f ⊙∘ ⊙fwin <I) (g <J)) ⟩
    Group.sum (C n (⊙Lift (⊙Sphere (S m)))) (λ <J →
      Group.exp (C n (⊙Lift (⊙Sphere (S m)))) (g <J) (⊙LiftSphereS-endo-degree m (⊙fwproj <J ⊙∘ f ⊙∘ ⊙fwin <I)))
        =∎

  rephrase-in-degrees₁ : ∀ {I J : ℕ} (f : ⊙FinBouquetLift I (S m) ⊙→ ⊙FinBouquetLift J (S m))
    {G : Group₀} (iso : C n (⊙Lift (⊙Sphere (S m))) ≃ᴳ G) g
    → GroupIso.f (Πᴳ-emap-r _ (λ _ → iso))
        (CEl-finite-additive (FinBouquetLift-family I (S m))
          (CEl-fmap n f (is-equiv.g (C-finite-additive-is-equiv (FinBouquetLift-family J (S m)))
            (GroupIso.g (Πᴳ-emap-r _ (λ _ → iso)) g))))
    ∼ λ <I → Group.sum G (λ <J → Group.exp G (g <J) (⊙LiftSphereS-endo-degree m (⊙fwproj <J ⊙∘ f ⊙∘ ⊙fwin <I)))
  rephrase-in-degrees₁ {I} {J} f {G} iso g <I =
    GroupIso.f iso
      (CEl-fmap n (⊙fwin <I)
        (CEl-fmap n f (is-equiv.g (C-finite-additive-is-equiv (FinBouquetLift-family J (S m)))
          (GroupIso.g (Πᴳ-emap-r _ (λ _ → iso)) g))))
      =⟨ ap (GroupIso.f iso) $ rephrase-in-degrees₀ f (GroupIso.g (Πᴳ-emap-r _ (λ _ → iso)) g) <I ⟩
    GroupIso.f iso
      (Group.sum (C n (⊙Lift (⊙Sphere (S m)))) (λ <J →
        Group.exp (C n (⊙Lift (⊙Sphere (S m)))) (GroupIso.g iso (g <J))
          (⊙LiftSphereS-endo-degree m (⊙fwproj <J ⊙∘ f ⊙∘ ⊙fwin <I))))
      =⟨ GroupIso.pres-sum iso (λ <J →
          Group.exp (C n (⊙Lift (⊙Sphere (S m)))) (GroupIso.g iso (g <J))
            (⊙LiftSphereS-endo-degree m (⊙fwproj <J ⊙∘ f ⊙∘ ⊙fwin <I))) ⟩
    Group.sum G (λ <J →
      GroupIso.f iso
        (Group.exp (C n (⊙Lift (⊙Sphere (S m))))
          (GroupIso.g iso (g <J))
          (⊙LiftSphereS-endo-degree m (⊙fwproj <J ⊙∘ f ⊙∘ ⊙fwin <I))))
      =⟨ ap (Group.sum G) (λ= λ <J →
          GroupIso.pres-exp iso
            (GroupIso.g iso (g <J))
            (⊙LiftSphereS-endo-degree m (⊙fwproj <J ⊙∘ f ⊙∘ ⊙fwin <I))) ⟩
    Group.sum G (λ <J →
      Group.exp G
        (GroupIso.f iso (GroupIso.g iso (g <J)))
        (⊙LiftSphereS-endo-degree m (⊙fwproj <J ⊙∘ f ⊙∘ ⊙fwin <I)))
      =⟨ ap (Group.sum G) (λ= λ <J →
          ap (λ g → Group.exp G g (⊙LiftSphereS-endo-degree m (⊙fwproj <J ⊙∘ f ⊙∘ ⊙fwin <I))) $
            GroupIso.f-g iso (g <J)) ⟩
    Group.sum G (λ <J → Group.exp G (g <J) (⊙LiftSphereS-endo-degree m (⊙fwproj <J ⊙∘ f ⊙∘ ⊙fwin <I)))
      =∎

  rephrase-in-degrees₂ : ∀ {I J : ℕ} (f : ⊙FinBouquet I (S m) ⊙→ ⊙FinBouquet J (S m))
    {G : Group₀} (iso : C n (⊙Lift (⊙Sphere (S m))) ≃ᴳ G) g
    → GroupIso.f (Πᴳ-emap-r _ (λ _ → iso))
        (CEl-finite-additive (FinBouquetLift-family I (S m))
          (CEl-fmap n (fst (⊙FinWedge-emap-r (λ _ → ⊙lower-equiv)))
            (CEl-fmap n f
              (CEl-fmap n (fst (⊙FinWedge-emap-r (λ _ → ⊙lower-equiv) ⊙⁻¹))
                (is-equiv.g (C-finite-additive-is-equiv (FinBouquetLift-family J (S m)))
                  (GroupIso.g (Πᴳ-emap-r _ (λ _ → iso)) g))))))
    ∼ λ <I → Group.sum G (λ <J → Group.exp G (g <J) (⊙SphereS-endo-degree m (⊙fwproj <J ⊙∘ f ⊙∘ ⊙fwin <I)))
  rephrase-in-degrees₂ {I} {J} f {G} iso g <I =
    GroupIso.f iso
      (CEl-fmap n (⊙fwin <I)
        (CEl-fmap n (fst (⊙FinWedge-emap-r (λ _ → ⊙lower-equiv)))
          (CEl-fmap n f
            (CEl-fmap n (fst (⊙FinWedge-emap-r (λ _ → ⊙lower-equiv) ⊙⁻¹))
              (is-equiv.g (C-finite-additive-is-equiv (FinBouquetLift-family J (S m)))
                (GroupIso.g (Πᴳ-emap-r _ (λ _ → iso)) g))))))
      =⟨ ap (GroupIso.f iso ∘ CEl-fmap n (⊙fwin <I)) $
          (λ x →
            ∘-CEl-fmap n (fst (⊙FinWedge-emap-r (λ _ → ⊙lower-equiv))) f
              (CEl-fmap n (fst (⊙FinWedge-emap-r (λ _ → ⊙lower-equiv) ⊙⁻¹)) x)
            ∙ ∘-CEl-fmap n (f ⊙∘ fst (⊙FinWedge-emap-r (λ _ → ⊙lower-equiv)))
                (fst (⊙FinWedge-emap-r (λ _ → ⊙lower-equiv) ⊙⁻¹)) x)
          (is-equiv.g (C-finite-additive-is-equiv (FinBouquetLift-family J (S m)))
            (GroupIso.g (Πᴳ-emap-r _ (λ _ → iso)) g)) ⟩
    GroupIso.f iso
      (CEl-fmap n (⊙fwin <I)
        (CEl-fmap n (fst (⊙FinWedge-emap-r (λ _ → ⊙lower-equiv) ⊙⁻¹) ⊙∘ f ⊙∘ fst (⊙FinWedge-emap-r (λ _ → ⊙lower-equiv)))
          (is-equiv.g (C-finite-additive-is-equiv (FinBouquetLift-family J (S m)))
            (GroupIso.g (Πᴳ-emap-r _ (λ _ → iso)) g))))
      =⟨ rephrase-in-degrees₁
          (fst (⊙FinWedge-emap-r (λ _ → ⊙lower-equiv) ⊙⁻¹) ⊙∘ f ⊙∘ fst (⊙FinWedge-emap-r (λ _ → ⊙lower-equiv)))
          iso g <I ⟩
    Group.sum G (λ <J → Group.exp G (g <J)
      (⊙LiftSphereS-endo-degree {i = lzero} m
        (⊙fwproj <J
        ⊙∘ (fst (⊙FinWedge-emap-r (λ _ → ⊙lower-equiv) ⊙⁻¹) ⊙∘ f ⊙∘ fst (⊙FinWedge-emap-r (λ _ → ⊙lower-equiv)))
        ⊙∘ ⊙fwin <I)))
      =⟨ ap (Group.sum G) (λ= λ <J →
          ap (Group.exp G (g <J)) $
            ⊙SphereS-endo-degree-base-indep m λ x →
              lower (fwproj <J (fst (FinWedge-emap-r (λ _ → ⊙lift-equiv)) (fst f (fwin <I x))))
                =⟨ ap lower (fwproj-FinWedge-emap-r-lift <J (fst f (fwin <I x))) ⟩
              fwproj <J (fst f (fwin <I x))
                =∎) ⟩
    Group.sum G (λ <J → Group.exp G (g <J)
      (⊙SphereS-endo-degree m (⊙fwproj <J ⊙∘ f ⊙∘ ⊙fwin <I)))
      =∎
