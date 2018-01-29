{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.Bouquet
open import homotopy.FinWedge
open import cohomology.Theory

module cohomology.FinBouquet (OT : OrdinaryTheory lzero) where

open OrdinaryTheory OT
open import cohomology.Sphere OT
open import cohomology.FinWedge cohomology-theory
open import cohomology.Bouquet OT

C-FinBouquet-diag : ∀ n I → C (ℕ-to-ℤ n) (⊙FinBouquet I n) ≃ᴳ Πᴳ (Fin I) (λ _ → C2 0)
C-FinBouquet-diag n I = C-Bouquet-diag n (Fin I) (Fin-has-choice 0 lzero)

abstract
  C-FinBouquet-diag-β : ∀ n I g <I
    →  GroupIso.f (C-FinBouquet-diag n I) g <I
    == GroupIso.f (C-Sphere-diag n)
        (CEl-fmap (ℕ-to-ℤ n) ⊙lower
          (CEl-fmap (ℕ-to-ℤ n) (⊙fwin <I) g))
  C-FinBouquet-diag-β n I g <I =
    GroupIso.f (C-Sphere-diag n) (CEl-fmap (ℕ-to-ℤ n) (⊙fwin <I) (CEl-fmap (ℕ-to-ℤ n) (⊙–> (⊙BigWedge-emap-r (λ _ → ⊙lower-equiv))) g))
      =⟨ ap (GroupIso.f (C-Sphere-diag n)) $
            ∘-CEl-fmap (ℕ-to-ℤ n) (⊙fwin <I) (⊙–> (⊙BigWedge-emap-r (λ _ → ⊙lower-equiv))) g
          ∙ CEl-fmap-base-indep (ℕ-to-ℤ n) (λ _ → idp) g
          ∙ CEl-fmap-∘ (ℕ-to-ℤ n) (⊙fwin <I) ⊙lower g ⟩
    GroupIso.f (C-Sphere-diag n) (CEl-fmap (ℕ-to-ℤ n) ⊙lower (CEl-fmap (ℕ-to-ℤ n) (⊙fwin <I) g))
      =∎
  
  inverse-C-FinBouquet-diag-β : ∀ n I g
    →  GroupIso.g (C-FinBouquet-diag n I) g
    == Group.sum (C (ℕ-to-ℤ n) (⊙FinBouquet I n))
        (λ <I → CEl-fmap (ℕ-to-ℤ n) (⊙fwproj <I)
          (CEl-fmap (ℕ-to-ℤ n) ⊙lift
            (GroupIso.g (C-Sphere-diag n) (g <I))))
  inverse-C-FinBouquet-diag-β n I g =
    GroupIso.g (C-FinBouquet-diag n I) g
      =⟨ idp ⟩
    CEl-fmap (ℕ-to-ℤ n) (⊙<– (⊙BigWedge-emap-r (λ _ → ⊙lower-equiv)))
      (GroupIso.g (C-finite-additive-iso (ℕ-to-ℤ n) (FinBouquetLift-family I n))
        (GroupIso.g (C-Sphere-diag n) ∘ g))
      =⟨ ap (CEl-fmap (ℕ-to-ℤ n) (⊙<– (⊙BigWedge-emap-r (λ _ → ⊙lower-equiv)))) $
          inverse-C-finite-additive-β (ℕ-to-ℤ n) (FinBouquetLift-family I n) (GroupIso.g (C-Sphere-diag n) ∘ g) ⟩
    CEl-fmap (ℕ-to-ℤ n) (⊙<– (⊙BigWedge-emap-r (λ _ → ⊙lower-equiv)))
      (Group.sum (C (ℕ-to-ℤ n) (⊙FinBouquetLift I n))
        (λ <I → CEl-fmap (ℕ-to-ℤ n) (⊙fwproj <I) (GroupIso.g (C-Sphere-diag n) (g <I))))
      =⟨ GroupHom.pres-sum (C-fmap (ℕ-to-ℤ n) (⊙<– (⊙BigWedge-emap-r (λ _ → ⊙lower-equiv)))) $
          (λ <I → CEl-fmap (ℕ-to-ℤ n) (⊙fwproj <I) (GroupIso.g (C-Sphere-diag n) (g <I))) ⟩
    Group.sum (C (ℕ-to-ℤ n) (⊙FinBouquet I n))
      (λ <I → 
        CEl-fmap (ℕ-to-ℤ n) (⊙<– (⊙BigWedge-emap-r (λ _ → ⊙lower-equiv)))
          (CEl-fmap (ℕ-to-ℤ n) (⊙fwproj <I) (GroupIso.g (C-Sphere-diag n) (g <I))))
      =⟨ ap (Group.sum (C (ℕ-to-ℤ n) (⊙FinBouquet I n)))
          (λ= λ <I →
              ∘-CEl-fmap (ℕ-to-ℤ n)
                (⊙<– (⊙BigWedge-emap-r (λ _ → ⊙lower-equiv))) (⊙fwproj <I)
                (GroupIso.g (C-Sphere-diag n) (g <I))
            ∙ CEl-fmap-base-indep (ℕ-to-ℤ n)
                (fwproj-FinWedge-emap-r-lift <I)
                (GroupIso.g (C-Sphere-diag n) (g <I))
            ∙ CEl-fmap-∘ (ℕ-to-ℤ n) ⊙lift (⊙fwproj <I)
                (GroupIso.g (C-Sphere-diag n) (g <I))) ⟩
    Group.sum (C (ℕ-to-ℤ n) (⊙FinBouquet I n))
      (λ <I →
        CEl-fmap (ℕ-to-ℤ n) (⊙fwproj <I)
          (CEl-fmap (ℕ-to-ℤ n) ⊙lift
            (GroupIso.g (C-Sphere-diag n) (g <I))))
      =∎
