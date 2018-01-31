{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.FinWedge
open import homotopy.Bouquet
open import groups.SphereEndomorphism
open import cohomology.Theory

module cohomology.RephraseSubFinCoboundary (OT : OrdinaryTheory lzero) where

open OrdinaryTheory OT
open import cohomology.SphereEndomorphism cohomology-theory
open import cohomology.Sphere OT
open import cohomology.SubFinBouquet OT

abstract
  rephrase-in-degree : ∀ n {I : ℕ} {JA JB : Type₀}
    (JB-ac : has-choice 0 JB lzero)
    (JB-dec : has-dec-eq JB)
    {J} (p : Fin J ≃ Coprod JA JB)
    (f : ⊙FinBouquet I (S n) ⊙→ ⊙Susp (⊙Bouquet JB n)) g
    → GroupIso.f (C-FinBouquet-diag (S n) I)
        (CEl-fmap (ℕ-to-ℤ (S n)) f
          (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Bouquet JB n))
            (GroupIso.g (C-SubFinBouquet-diag n JB-ac (–> p)) g)))
    ∼ λ <I → Group.subsum-r (C2 0) (–> p)
          (λ b → Group.exp (C2 0) (g b) (⊙SphereS-endo-degree n (⊙Susp-fmap (⊙bwproj JB-dec b) ⊙∘ f ⊙∘ ⊙fwin <I)))
  rephrase-in-degree n {I} {JA} {JB} JB-ac JB-dec {J} p f g <I =
    GroupIso.f (C-FinBouquet-diag (S n) I)
      (CEl-fmap (ℕ-to-ℤ (S n)) f
        (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Bouquet JB n))
          (GroupIso.g (C-SubFinBouquet-diag n JB-ac (–> p)) g)))
      <I
      =⟨ ap
          (λ g → GroupIso.f (C-FinBouquet-diag (S n) I)
            (CEl-fmap (ℕ-to-ℤ (S n)) f
              (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Bouquet JB n))
                g)) <I)
          (inverse-C-SubFinBouquet-diag-β n JB-ac JB-dec p g) ⟩
    GroupIso.f (C-FinBouquet-diag (S n) I)
      (CEl-fmap (ℕ-to-ℤ (S n)) f
        (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Bouquet JB n))
          (Group.subsum-r (C (ℕ-to-ℤ n) (⊙Bouquet JB n)) (–> p)
            (λ b → CEl-fmap (ℕ-to-ℤ n) (⊙bwproj JB-dec b)
              (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                (GroupIso.g (C-Sphere-diag n) (g b)))))))
      <I
      =⟨ ap (λ g → GroupIso.f (C-FinBouquet-diag (S n) I) g <I) $
          GroupHom.pres-subsum-r
            (C-fmap (ℕ-to-ℤ (S n)) f ∘ᴳ GroupIso.g-hom (C-Susp (ℕ-to-ℤ n) (⊙Bouquet JB n)))
            (–> p)
            (λ b → CEl-fmap (ℕ-to-ℤ n) (⊙bwproj JB-dec b)
              (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                (GroupIso.g (C-Sphere-diag n) (g b)))) ⟩
    GroupIso.f (C-FinBouquet-diag (S n) I)
      (Group.subsum-r (C (ℕ-to-ℤ (S n)) (⊙FinBouquet I (S n))) (–> p)
        (λ b → CEl-fmap (ℕ-to-ℤ (S n)) f
          (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Bouquet JB n))
            (CEl-fmap (ℕ-to-ℤ n) (⊙bwproj JB-dec b)
              (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                (GroupIso.g (C-Sphere-diag n) (g b)))))))
      <I
      =⟨ ap
          (λ f → GroupIso.f (C-FinBouquet-diag (S n) I)
            (Group.subsum-r (C (ℕ-to-ℤ (S n)) (⊙FinBouquet I (S n))) (–> p) f) <I)
          (λ= λ b → ap (CEl-fmap (ℕ-to-ℤ (S n)) f) $
            C-Susp-fmap' (ℕ-to-ℤ n) (⊙bwproj JB-dec b) □$ᴳ
              CEl-fmap (ℕ-to-ℤ n) ⊙lift (GroupIso.g (C-Sphere-diag n) (g b))) ⟩
    GroupIso.f (C-FinBouquet-diag (S n) I)
      (Group.subsum-r (C (ℕ-to-ℤ (S n)) (⊙FinBouquet I (S n))) (–> p)
        (λ b → CEl-fmap (ℕ-to-ℤ (S n)) f
          (CEl-fmap (ℕ-to-ℤ (S n)) (⊙Susp-fmap (⊙bwproj JB-dec b))
            (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Sphere n))
              (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                (GroupIso.g (C-Sphere-diag n) (g b)))))))
      <I
      =⟨ C-FinBouquet-diag-β (S n) I
          (Group.subsum-r (C (ℕ-to-ℤ (S n)) (⊙FinBouquet I (S n))) (–> p)
            (λ b → CEl-fmap (ℕ-to-ℤ (S n)) f
              (CEl-fmap (ℕ-to-ℤ (S n)) (⊙Susp-fmap (⊙bwproj JB-dec b))
                (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Sphere n))
                  (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                    (GroupIso.g (C-Sphere-diag n) (g b)))))))
          <I ⟩
    GroupIso.f (C-Sphere-diag (S n))
      (CEl-fmap (ℕ-to-ℤ (S n)) ⊙lower
        (CEl-fmap (ℕ-to-ℤ (S n)) (⊙fwin <I)
          (Group.subsum-r (C (ℕ-to-ℤ (S n)) (⊙FinBouquet I (S n))) (–> p)
            (λ b → CEl-fmap (ℕ-to-ℤ (S n)) f
              (CEl-fmap (ℕ-to-ℤ (S n)) (⊙Susp-fmap (⊙bwproj JB-dec b))
                (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Sphere n))
                  (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                    (GroupIso.g (C-Sphere-diag n) (g b)))))))))
      =⟨ GroupHom.pres-subsum-r
          (  GroupIso.f-hom (C-Sphere-diag (S n))
          ∘ᴳ C-fmap (ℕ-to-ℤ (S n)) ⊙lower
          ∘ᴳ C-fmap (ℕ-to-ℤ (S n)) (⊙fwin <I))
          (–> p)
          (λ b → CEl-fmap (ℕ-to-ℤ (S n)) f
            (CEl-fmap (ℕ-to-ℤ (S n)) (⊙Susp-fmap (⊙bwproj JB-dec b))
              (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Sphere n))
                (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                  (GroupIso.g (C-Sphere-diag n) (g b)))))) ⟩
    Group.subsum-r (C2 0) (–> p)
      (λ b → GroupIso.f (C-Sphere-diag (S n))
        (CEl-fmap (ℕ-to-ℤ (S n)) ⊙lower
          (CEl-fmap (ℕ-to-ℤ (S n)) (⊙fwin <I)
            (CEl-fmap (ℕ-to-ℤ (S n)) f
              (CEl-fmap (ℕ-to-ℤ (S n)) (⊙Susp-fmap (⊙bwproj JB-dec b))
                (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Sphere n))
                  (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                    (GroupIso.g (C-Sphere-diag n) (g b)))))))))
      =⟨ ap (Group.subsum-r (C2 0) (–> p))
          (λ= λ b → ap (GroupIso.f (C-Sphere-diag (S n)) ∘ CEl-fmap (ℕ-to-ℤ (S n)) ⊙lower) $
              ∘-CEl-fmap (ℕ-to-ℤ (S n)) (⊙fwin <I) f _
            ∙ ∘-CEl-fmap (ℕ-to-ℤ (S n)) (f ⊙∘ ⊙fwin <I) (⊙Susp-fmap (⊙bwproj JB-dec b)) _
            ∙ CEl-fmap-⊙Sphere-endo-η (ℕ-to-ℤ (S n)) n
                (⊙Susp-fmap (⊙bwproj JB-dec b) ⊙∘ f ⊙∘ ⊙fwin <I)
                (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Sphere n))
                  (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                    (GroupIso.g (C-Sphere-diag n) (g b))))) ⟩
    Group.subsum-r (C2 0) (–> p)
      (λ b → GroupIso.f (C-Sphere-diag (S n))
        (CEl-fmap (ℕ-to-ℤ (S n)) ⊙lower
          (Group.exp (C (ℕ-to-ℤ (S n)) (⊙Sphere (S n)))
            (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Sphere n))
              (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                (GroupIso.g (C-Sphere-diag n) (g b))))
            (⊙SphereS-endo-degree n (⊙Susp-fmap (⊙bwproj JB-dec b) ⊙∘ f ⊙∘ ⊙fwin <I)))))
      =⟨ ap (Group.subsum-r (C2 0) (–> p))
          (λ= λ b →
            GroupHom.pres-exp
              (GroupIso.f-hom (C-Sphere-diag (S n)) ∘ᴳ C-fmap (ℕ-to-ℤ (S n)) ⊙lower)
              (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Sphere n))
                (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                  (GroupIso.g (C-Sphere-diag n) (g b))))
              (⊙SphereS-endo-degree n (⊙Susp-fmap (⊙bwproj JB-dec b) ⊙∘ f ⊙∘ ⊙fwin <I))) ⟩
    Group.subsum-r (C2 0) (–> p)
      (λ b → Group.exp (C2 0)
        (GroupIso.f (C-Sphere-diag n)
          (–> (CEl-Susp (ℕ-to-ℤ n) (⊙Lift (⊙Sphere n)))
            (CEl-fmap (ℕ-to-ℤ (S n)) (⊙lift {j = lzero} ⊙∘ ⊙Susp-fmap {Y = ⊙Sphere n} ⊙lower)
              (CEl-fmap (ℕ-to-ℤ (S n)) ⊙lower
                (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Sphere n))
                  (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                    (GroupIso.g (C-Sphere-diag n) (g b))))))))
        (⊙SphereS-endo-degree n (⊙Susp-fmap (⊙bwproj JB-dec b) ⊙∘ f ⊙∘ ⊙fwin <I)))
      =⟨ ap (Group.subsum-r (C2 0) (–> p))
          (λ= λ b → ap (λ g → Group.exp (C2 0) g (⊙SphereS-endo-degree n (⊙Susp-fmap (⊙bwproj JB-dec b) ⊙∘ f ⊙∘ ⊙fwin <I))) $
            ap (GroupIso.f (C-Sphere-diag n) ∘ –> (CEl-Susp (ℕ-to-ℤ n) (⊙Lift (⊙Sphere n))))
              ( CEl-fmap-∘ (ℕ-to-ℤ (S n)) ⊙lift (⊙Susp-fmap {Y = ⊙Sphere n} ⊙lower) _
              ∙ ap (CEl-fmap (ℕ-to-ℤ (S n)) (⊙Susp-fmap {Y = ⊙Sphere n} ⊙lower))
                  ( ∘-CEl-fmap (ℕ-to-ℤ (S n)) ⊙lift ⊙lower _
                  ∙ CEl-fmap-idf (ℕ-to-ℤ (S n)) _))
            ∙ ap (GroupIso.f (C-Sphere-diag n))
                ( (C-Susp-fmap (ℕ-to-ℤ n) ⊙lower □$ᴳ _)
                ∙ ap (CEl-fmap (ℕ-to-ℤ n) ⊙lower) (GroupIso.f-g (C-Susp (ℕ-to-ℤ n) (⊙Sphere n)) _)
                ∙ ∘-CEl-fmap (ℕ-to-ℤ n) ⊙lower ⊙lift _
                ∙ CEl-fmap-idf (ℕ-to-ℤ n) _)
            ∙ GroupIso.f-g (C-Sphere-diag n) (g b)) ⟩
    Group.subsum-r (C2 0) (–> p)
      (λ b → Group.exp (C2 0) (g b)
        (⊙SphereS-endo-degree n (⊙Susp-fmap (⊙bwproj JB-dec b) ⊙∘ f ⊙∘ ⊙fwin <I)))
      =∎

  rephrase-in-degree' : ∀ n {I J : ℕ} (f : ⊙FinBouquet I (S n) ⊙→ ⊙Susp (⊙FinBouquet J n)) g
    → GroupIso.f (C-FinBouquet-diag (S n) I)
        (CEl-fmap (ℕ-to-ℤ (S n)) f
          (<– (CEl-Susp (ℕ-to-ℤ n) (⊙FinBouquet J n))
            (GroupIso.g (C-FinBouquet-diag n J) g)))
    ∼ λ <I → Group.sum (C2 0)
          (λ <J → Group.exp (C2 0) (g <J) (⊙SphereS-endo-degree n (⊙Susp-fmap (⊙fwproj <J) ⊙∘ f ⊙∘ ⊙fwin <I)))
  rephrase-in-degree' n {I} {J} f g =
    rephrase-in-degree n {I} {JA = Empty} {JB = Fin J}
      (Fin-has-choice 0 lzero) Fin-has-dec-eq (⊔₁-Empty (Fin J) ⁻¹) f g
