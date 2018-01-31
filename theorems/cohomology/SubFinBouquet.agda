{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.Bouquet
open import homotopy.FinWedge
open import cohomology.Theory

module cohomology.SubFinBouquet (OT : OrdinaryTheory lzero) where

open OrdinaryTheory OT
open import cohomology.Sphere OT
open import cohomology.SubFinWedge cohomology-theory
open import cohomology.Bouquet OT

C-SubFinBouquet-diag : ∀ n {A B : Type₀} (B-ac : has-choice 0 B lzero) {I} (p : Fin I → Coprod A B)
  → C (ℕ-to-ℤ n) (⊙Bouquet B n) ≃ᴳ Πᴳ B (λ _ → C2 0)
C-SubFinBouquet-diag n {B = B} B-ac p = C-Bouquet-diag n B B-ac

C-FinBouquet-diag : ∀ n I → C (ℕ-to-ℤ n) (⊙FinBouquet I n) ≃ᴳ Πᴳ (Fin I) (λ _ → C2 0)
C-FinBouquet-diag n I = C-SubFinBouquet-diag n {A = Empty} {B = Fin I} (Fin-has-choice 0 lzero) inr

abstract
  C-SubFinBouquet-diag-β : ∀ n {A B : Type₀} (B-ac : has-choice 0 B lzero) {I} (p : Fin I → Coprod A B) g b
    →  GroupIso.f (C-FinBouquet-diag n I) g b
    == GroupIso.f (C-Sphere-diag n)
        (CEl-fmap (ℕ-to-ℤ n) ⊙lower
          (CEl-fmap (ℕ-to-ℤ n) (⊙bwin b) g))
  C-SubFinBouquet-diag-β n B-ac p g b =
    GroupIso.f (C-Sphere-diag n)
      (CEl-fmap (ℕ-to-ℤ n) (⊙bwin b)
        (CEl-fmap (ℕ-to-ℤ n) (⊙–> (⊙BigWedge-emap-r (λ _ → ⊙lower-equiv))) g))
      =⟨ ap (GroupIso.f (C-Sphere-diag n)) $
            ∘-CEl-fmap (ℕ-to-ℤ n) (⊙bwin b) (⊙–> (⊙BigWedge-emap-r (λ _ → ⊙lower-equiv))) g
          ∙ CEl-fmap-base-indep (ℕ-to-ℤ n) (λ _ → idp) g
          ∙ CEl-fmap-∘ (ℕ-to-ℤ n) (⊙bwin b) ⊙lower g ⟩
    GroupIso.f (C-Sphere-diag n) (CEl-fmap (ℕ-to-ℤ n) ⊙lower (CEl-fmap (ℕ-to-ℤ n) (⊙bwin b) g))
      =∎
  
  C-FinBouquet-diag-β : ∀ n I g <I
    →  GroupIso.f (C-FinBouquet-diag n I) g <I
    == GroupIso.f (C-Sphere-diag n)
        (CEl-fmap (ℕ-to-ℤ n) ⊙lower
          (CEl-fmap (ℕ-to-ℤ n) (⊙bwin <I) g))
  C-FinBouquet-diag-β n I =
    C-SubFinBouquet-diag-β n {A = Empty} {B = Fin I}
      (Fin-has-choice 0 lzero) inr

  inverse-C-SubFinBouquet-diag-β : ∀ n
    {A B : Type₀} (B-ac : has-choice 0 B lzero) (B-dec : has-dec-eq B) {I} (p : Fin I ≃ Coprod A B) g
    →  GroupIso.g (C-SubFinBouquet-diag n B-ac (–> p)) g
    == Group.subsum-r (C (ℕ-to-ℤ n) (⊙Bouquet B n)) (–> p)
        (λ b → CEl-fmap (ℕ-to-ℤ n) (⊙bwproj B-dec b)
          (CEl-fmap (ℕ-to-ℤ n) ⊙lift
            (GroupIso.g (C-Sphere-diag n) (g b))))
  inverse-C-SubFinBouquet-diag-β n {B = B} B-ac B-dec p g =
    CEl-fmap (ℕ-to-ℤ n) (⊙<– (⊙BigWedge-emap-r (λ _ → ⊙lower-equiv)))
      (GroupIso.g (C-subfinite-additive-iso (ℕ-to-ℤ n) (–> p) (⊙Lift (⊙Sphere n)) B-ac)
        (GroupIso.g (C-Sphere-diag n) ∘ g))
      =⟨ ap (CEl-fmap (ℕ-to-ℤ n) (⊙<– (⊙BigWedge-emap-r (λ _ → ⊙lower-equiv)))) $
          inverse-C-subfinite-additive-β (ℕ-to-ℤ n) B-ac B-dec p (GroupIso.g (C-Sphere-diag n) ∘ g) ⟩
    CEl-fmap (ℕ-to-ℤ n) (⊙<– (⊙BigWedge-emap-r (λ _ → ⊙lower-equiv)))
      (Group.subsum-r (C (ℕ-to-ℤ n) (⊙BouquetLift B n)) (–> p)
        (λ b → CEl-fmap (ℕ-to-ℤ n) (⊙bwproj B-dec b) (GroupIso.g (C-Sphere-diag n) (g b))))
      =⟨ GroupHom.pres-subsum-r (C-fmap (ℕ-to-ℤ n) (⊙<– (⊙BigWedge-emap-r (λ _ → ⊙lower-equiv)))) (–> p) $
          (λ b → CEl-fmap (ℕ-to-ℤ n) (⊙bwproj B-dec b) (GroupIso.g (C-Sphere-diag n) (g b))) ⟩
    Group.subsum-r (C (ℕ-to-ℤ n) (⊙Bouquet B n)) (–> p)
      (λ b →
        CEl-fmap (ℕ-to-ℤ n) (⊙<– (⊙BigWedge-emap-r (λ _ → ⊙lower-equiv)))
          (CEl-fmap (ℕ-to-ℤ n) (⊙bwproj B-dec b) (GroupIso.g (C-Sphere-diag n) (g b))))
      =⟨ ap (Group.subsum-r (C (ℕ-to-ℤ n) (⊙Bouquet B n)) (–> p))
          (λ= λ b →
              ∘-CEl-fmap (ℕ-to-ℤ n)
                (⊙<– (⊙BigWedge-emap-r (λ _ → ⊙lower-equiv))) (⊙bwproj B-dec b)
                (GroupIso.g (C-Sphere-diag n) (g b))
            ∙ CEl-fmap-base-indep (ℕ-to-ℤ n)
                (bwproj-BigWedge-emap-r-lift B-dec b)
                (GroupIso.g (C-Sphere-diag n) (g b))
            ∙ CEl-fmap-∘ (ℕ-to-ℤ n) ⊙lift (⊙bwproj B-dec b)
                (GroupIso.g (C-Sphere-diag n) (g b))) ⟩
    Group.subsum-r (C (ℕ-to-ℤ n) (⊙Bouquet B n)) (–> p)
      (λ b →
        CEl-fmap (ℕ-to-ℤ n) (⊙bwproj B-dec b)
          (CEl-fmap (ℕ-to-ℤ n) ⊙lift
            (GroupIso.g (C-Sphere-diag n) (g b))))
      =∎

  inverse-C-FinBouquet-diag-β : ∀ n I g
    →  GroupIso.g (C-FinBouquet-diag n I) g
    == Group.sum (C (ℕ-to-ℤ n) (⊙FinBouquet I n))
        (λ <I → CEl-fmap (ℕ-to-ℤ n) (⊙fwproj <I)
          (CEl-fmap (ℕ-to-ℤ n) ⊙lift
            (GroupIso.g (C-Sphere-diag n) (g <I))))
  inverse-C-FinBouquet-diag-β n I =
    inverse-C-SubFinBouquet-diag-β n {A = Empty} {B = Fin I}
      (Fin-has-choice 0 lzero) Fin-has-dec-eq (⊔₁-Empty (Fin I) ⁻¹)
