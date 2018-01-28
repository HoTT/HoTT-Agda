{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.FinWedge
open import homotopy.Bouquet
open import groups.FinProduct 
open import groups.SphereEndomorphism
open import cohomology.Theory

module cohomology.RephraseFinCoboundary (OT : OrdinaryTheory lzero) where

open OrdinaryTheory OT
open import cohomology.FinWedge cohomology-theory
open import cohomology.SphereEndomorphism cohomology-theory
open import cohomology.Sphere OT
open import cohomology.FinBouquet OT

abstract
  rephrase-in-degree : ∀ n {I J : ℕ} (f : ⊙FinBouquet I (S n) ⊙→ ⊙Susp (⊙FinBouquet J n)) g
    → GroupIso.f (C-FinBouquet-diag (S n) I)
        (CEl-fmap (ℕ-to-ℤ (S n)) f
          (<– (CEl-Susp (ℕ-to-ℤ n) (⊙FinBouquet J n))
            (GroupIso.g (C-FinBouquet-diag n J) g)))
    ∼ λ <I → Group.sum (C2 0)
          (λ <J → Group.exp (C2 0) (g <J) (⊙SphereS-endo-degree n (⊙Susp-fmap (⊙fwproj <J) ⊙∘ f ⊙∘ ⊙fwin <I)))
  rephrase-in-degree n {I} {J} f g <I =
    GroupIso.f (C-FinBouquet-diag (S n) I)
      (CEl-fmap (ℕ-to-ℤ (S n)) f
        (<– (CEl-Susp (ℕ-to-ℤ n) (⊙FinBouquet J n))
          (GroupIso.g (C-FinBouquet-diag n J) g)))
      <I
      =⟨ ap
          (λ g → GroupIso.f (C-FinBouquet-diag (S n) I)
            (CEl-fmap (ℕ-to-ℤ (S n)) f
              (<– (CEl-Susp (ℕ-to-ℤ n) (⊙FinBouquet J n))
                g)) <I)
          (inverse-C-FinBouquet-diag-β n J g) ⟩
    GroupIso.f (C-FinBouquet-diag (S n) I)
      (CEl-fmap (ℕ-to-ℤ (S n)) f
        (<– (CEl-Susp (ℕ-to-ℤ n) (⊙FinBouquet J n))
          (Group.sum (C (ℕ-to-ℤ n) (⊙FinBouquet J n))
            (λ <J → CEl-fmap (ℕ-to-ℤ n) (⊙fwproj <J)
              (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                (GroupIso.g (C-Sphere-diag n) (g <J)))))))
      <I
      =⟨ ap (λ g → GroupIso.f (C-FinBouquet-diag (S n) I) g <I) $
          GroupHom.pres-sum
            (C-fmap (ℕ-to-ℤ (S n)) f ∘ᴳ GroupIso.g-hom (C-Susp (ℕ-to-ℤ n) (⊙FinBouquet J n)))
            (λ <J → CEl-fmap (ℕ-to-ℤ n) (⊙fwproj <J)
              (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                (GroupIso.g (C-Sphere-diag n) (g <J)))) ⟩
    GroupIso.f (C-FinBouquet-diag (S n) I)
      (Group.sum (C (ℕ-to-ℤ (S n)) (⊙FinBouquet I (S n)))
        (λ <J → CEl-fmap (ℕ-to-ℤ (S n)) f
          (<– (CEl-Susp (ℕ-to-ℤ n) (⊙FinBouquet J n))
            (CEl-fmap (ℕ-to-ℤ n) (⊙fwproj <J)
              (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                (GroupIso.g (C-Sphere-diag n) (g <J)))))))
      <I
      =⟨ ap
          (λ f → GroupIso.f (C-FinBouquet-diag (S n) I)
            (Group.sum (C (ℕ-to-ℤ (S n)) (⊙FinBouquet I (S n))) f) <I)
          (λ= λ <J → ap (CEl-fmap (ℕ-to-ℤ (S n)) f) $
            C-Susp-fmap' (ℕ-to-ℤ n) (⊙fwproj <J) □$ᴳ
              CEl-fmap (ℕ-to-ℤ n) ⊙lift (GroupIso.g (C-Sphere-diag n) (g <J))) ⟩
    GroupIso.f (C-FinBouquet-diag (S n) I)
      (Group.sum (C (ℕ-to-ℤ (S n)) (⊙FinBouquet I (S n)))
        (λ <J → CEl-fmap (ℕ-to-ℤ (S n)) f
          (CEl-fmap (ℕ-to-ℤ (S n)) (⊙Susp-fmap (⊙fwproj <J))
            (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Sphere n))
              (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                (GroupIso.g (C-Sphere-diag n) (g <J)))))))
      <I
      =⟨ C-FinBouquet-diag-β (S n) I
          (Group.sum (C (ℕ-to-ℤ (S n)) (⊙FinBouquet I (S n)))
            (λ <J → CEl-fmap (ℕ-to-ℤ (S n)) f
              (CEl-fmap (ℕ-to-ℤ (S n)) (⊙Susp-fmap (⊙fwproj <J))
                (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Sphere n))
                  (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                    (GroupIso.g (C-Sphere-diag n) (g <J)))))))
          <I ⟩
    GroupIso.f (C-Sphere-diag (S n))
      (CEl-fmap (ℕ-to-ℤ (S n)) ⊙lower
        (CEl-fmap (ℕ-to-ℤ (S n)) (⊙fwin <I)
          (Group.sum (C (ℕ-to-ℤ (S n)) (⊙FinBouquet I (S n)))
            (λ <J → CEl-fmap (ℕ-to-ℤ (S n)) f
              (CEl-fmap (ℕ-to-ℤ (S n)) (⊙Susp-fmap (⊙fwproj <J))
                (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Sphere n))
                  (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                    (GroupIso.g (C-Sphere-diag n) (g <J)))))))))
      =⟨ GroupHom.pres-sum
          (  GroupIso.f-hom (C-Sphere-diag (S n))
          ∘ᴳ C-fmap (ℕ-to-ℤ (S n)) ⊙lower
          ∘ᴳ C-fmap (ℕ-to-ℤ (S n)) (⊙fwin <I))
          (λ <J → CEl-fmap (ℕ-to-ℤ (S n)) f
            (CEl-fmap (ℕ-to-ℤ (S n)) (⊙Susp-fmap (⊙fwproj <J))
              (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Sphere n))
                (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                  (GroupIso.g (C-Sphere-diag n) (g <J)))))) ⟩
    Group.sum (C2 0)
      (λ <J → GroupIso.f (C-Sphere-diag (S n))
        (CEl-fmap (ℕ-to-ℤ (S n)) ⊙lower
          (CEl-fmap (ℕ-to-ℤ (S n)) (⊙fwin <I)
            (CEl-fmap (ℕ-to-ℤ (S n)) f
              (CEl-fmap (ℕ-to-ℤ (S n)) (⊙Susp-fmap (⊙fwproj <J))
                (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Sphere n))
                  (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                    (GroupIso.g (C-Sphere-diag n) (g <J)))))))))
      =⟨ ap (Group.sum (C2 0))
          (λ= λ <J → ap (GroupIso.f (C-Sphere-diag (S n)) ∘ CEl-fmap (ℕ-to-ℤ (S n)) ⊙lower) $
              ∘-CEl-fmap (ℕ-to-ℤ (S n)) (⊙fwin <I) f _
            ∙ ∘-CEl-fmap (ℕ-to-ℤ (S n)) (f ⊙∘ ⊙fwin <I) (⊙Susp-fmap (⊙fwproj <J)) _
            ∙ CEl-fmap-⊙Sphere-endo-η (ℕ-to-ℤ (S n)) n
                (⊙Susp-fmap (⊙fwproj <J) ⊙∘ f ⊙∘ ⊙fwin <I)
                (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Sphere n))
                  (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                    (GroupIso.g (C-Sphere-diag n) (g <J))))) ⟩
    Group.sum (C2 0)
      (λ <J → GroupIso.f (C-Sphere-diag (S n))
        (CEl-fmap (ℕ-to-ℤ (S n)) ⊙lower
          (Group.exp (C (ℕ-to-ℤ (S n)) (⊙Sphere (S n)))
            (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Sphere n))
              (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                (GroupIso.g (C-Sphere-diag n) (g <J))))
            (⊙SphereS-endo-degree n (⊙Susp-fmap (⊙fwproj <J) ⊙∘ f ⊙∘ ⊙fwin <I)))))
      =⟨ ap (Group.sum (C2 0))
          (λ= λ <J →
            GroupHom.pres-exp
              (GroupIso.f-hom (C-Sphere-diag (S n)) ∘ᴳ C-fmap (ℕ-to-ℤ (S n)) ⊙lower)
              (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Sphere n))
                (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                  (GroupIso.g (C-Sphere-diag n) (g <J))))
              (⊙SphereS-endo-degree n (⊙Susp-fmap (⊙fwproj <J) ⊙∘ f ⊙∘ ⊙fwin <I))) ⟩
    Group.sum (C2 0)
      (λ <J → Group.exp (C2 0)
        (GroupIso.f (C-Sphere-diag n)
          (–> (CEl-Susp (ℕ-to-ℤ n) (⊙Lift (⊙Sphere n)))
            (CEl-fmap (ℕ-to-ℤ (S n)) (⊙lift {j = lzero} ⊙∘ ⊙Susp-fmap {Y = ⊙Sphere n} ⊙lower)
              (CEl-fmap (ℕ-to-ℤ (S n)) ⊙lower
                (<– (CEl-Susp (ℕ-to-ℤ n) (⊙Sphere n))
                  (CEl-fmap (ℕ-to-ℤ n) ⊙lift
                    (GroupIso.g (C-Sphere-diag n) (g <J))))))))
        (⊙SphereS-endo-degree n (⊙Susp-fmap (⊙fwproj <J) ⊙∘ f ⊙∘ ⊙fwin <I)))
      =⟨ ap (Group.sum (C2 0))
          (λ= λ <J → ap (λ g → Group.exp (C2 0) g (⊙SphereS-endo-degree n (⊙Susp-fmap (⊙fwproj <J) ⊙∘ f ⊙∘ ⊙fwin <I))) $
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
            ∙ GroupIso.f-g (C-Sphere-diag n) (g <J)) ⟩
    Group.sum (C2 0)
      (λ <J → Group.exp (C2 0) (g <J)
        (⊙SphereS-endo-degree n (⊙Susp-fmap (⊙fwproj <J) ⊙∘ f ⊙∘ ⊙fwin <I)))
      =∎
