{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.HSpace

module homotopy.KG1HSpace where

module KG1HSpace {i} (A : Group i) (A-abelian : is-abelian A) where

  module A = Group A
  open KG1 A

  mult-loop : (g : A.El) (x : KG1) → x == x
  mult-loop g = KG1-elim
    {P = λ x → x == x}
    (λ _ → =-preserves-level _ klevel)
    (kloop g)
    loop'
    (set-↓-has-all-paths-↓ (klevel kbase kbase))
    (λ _ _ → set-↓-has-all-paths-↓ (klevel kbase kbase))
    where
    abstract
      loop' : (g' : A.El) → kloop g == kloop g [ (λ x → x == x) ↓ kloop g' ]
      loop' g' = ↓-idf=idf-in $
        kloop g ∙ kloop g'     =⟨ ! (kloop-comp g g') ⟩
        kloop (A.comp g g')      =⟨ ap kloop (A-abelian g g') ⟩
        kloop (A.comp g' g)      =⟨ kloop-comp g' g ⟩
        kloop g' ∙ kloop g     =⟨ ∙=∙' (kloop g') (kloop g) ⟩
        kloop g' ∙' kloop g    ∎

  mult-hom : GroupHom A
    (Ω^-Group 1 ((KG1 → KG1) , (λ x → x)) (Π-level (λ _ → klevel)))
  mult-hom = record {f = f; pres-ident = pres-ident; pres-comp = pres-comp}
    where
    f = λ g → λ= (mult-loop g)

    pres-ident =
      ap λ= (λ= (KG1-elim
        {P = λ x → mult-loop A.ident x == app= (idp {a = idf _}) x}
        (λ _ → =-preserves-level _ (=-preserves-level _ klevel))
        (kloop-ident ∙ ! (ap-idf idp))
        (λ _ → prop-has-all-paths-↓ (klevel _ _ _ _))
        (set-↓-has-all-paths-↓ (=-preserves-level _ (klevel _ _)))
        (λ _ _ → set-↓-has-all-paths-↓ (=-preserves-level _ (klevel _ _)))))
      ∙ ! (λ=-η idp)

    pres-comp = λ g₁ g₂ →
      ap λ= (λ= (KG1-elim
        {P = λ x → mult-loop (A.comp g₁ g₂) x
                == mult-loop g₁ x ∙ mult-loop g₂ x}
        (λ _ →  =-preserves-level _ (=-preserves-level _ klevel))
        (kloop-comp g₁ g₂)
        (λ _ → prop-has-all-paths-↓ (klevel _ _ _ _))
        (set-↓-has-all-paths-↓ (=-preserves-level _ (klevel _ _)))
        (λ _ _ → set-↓-has-all-paths-↓ (=-preserves-level _ (klevel _ _)))))
      ∙ ! (∙-λ= _ _)

  mult : KG1 → KG1 → KG1
  mult = KG1-rec {C = KG1 → KG1} (Π-level (λ _ → klevel)) (λ x → x) mult-hom

  H-KG1 : HSpaceStructure KG1
  H-KG1 = record { e = kbase; μ = mult; μe- = μe-; μ-e = μ-e}
    where
    μe- : (x : KG1) → mult kbase x == x
    μe- = KG1-elim
      {P = λ x → mult kbase x == x}
      (λ _ → =-preserves-level ⟨ 1 ⟩ klevel)
      idp
      (λ g → ↓-app=idf-in $ ∙'-unit-l (kloop g) ∙ (! (ap-idf (kloop g)))
                            ∙ ! (∙-unit-r (ap (mult kbase) (kloop g))))
      (set-↓-has-all-paths-↓ (klevel _ _))
      (λ _ _ → set-↓-has-all-paths-↓ (klevel _ _))

    μ-e : (x : KG1) → mult x kbase == x
    μ-e = KG1-elim
      {P = λ x → mult x kbase == x}
      (λ _ → =-preserves-level ⟨ 1 ⟩ klevel)
      idp
      (λ g → ↓-app=idf-in $
         idp ∙' kloop g
           =⟨ ∙'-unit-l (kloop g) ⟩
         kloop g
           =⟨ ! (app=-β (mult-loop g) kbase) ⟩
         app= (λ= (mult-loop g)) kbase
           =⟨ ! (KG1Rec.kloop-β {C = KG1 → KG1}
                   (Π-level (λ _ → klevel)) (λ x → x) mult-hom g)
              |in-ctx (λ w → app= w kbase) ⟩
         app= (ap mult (kloop g)) kbase
           =⟨ ∘-ap (λ f → f kbase) mult (kloop g) ⟩
         ap (λ z → mult z kbase) (kloop g)
           =⟨ ! (∙-unit-r (ap (λ z → mult z kbase) (kloop g))) ⟩
         ap (λ z → mult z kbase) (kloop g) ∙ idp ∎)
      (set-↓-has-all-paths-↓ (klevel _ _))
      (λ _ _ → set-↓-has-all-paths-↓ (klevel _ _))

  open HSpaceStructure H-KG1
  μcoh : μe- e == μ-e e
  μcoh = idp
