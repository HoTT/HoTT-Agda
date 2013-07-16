{-# OPTIONS --without-K #-}

open import HoTT
open import lib.Group
open import homotopy.HSpace
import lib.types.KG1

module homotopy.KG1HSpace {i} (A : AbelianGroup i) where

open Group (fst A)
open lib.types.KG1 (fst A)

mult-loop : (g : El) (x : KG1) → x == x
mult-loop g = KG1-elim 
  {C = λ x → ((x == x) , =-preserves-level _ klevel)}
  (kloop g)
  loop'
  (set-↓-has-all-paths-↓ (klevel kbase kbase))
  (λ _ _ → set-↓-has-all-paths-↓ (klevel kbase kbase))
  where
  abstract
    loop' : (g' : El) → kloop g == kloop g [ (λ x → x == x) ↓ kloop g' ]
    loop' g' = ↓-idf=idf-in $
      kloop g ∙ kloop g'     =⟨ ! (kloop-comp g g') ⟩
      kloop (comp g g')      =⟨ ap kloop (snd A g g') ⟩
      kloop (comp g' g)      =⟨ kloop-comp g' g ⟩
      kloop g' ∙ kloop g     =⟨ ∙=∙' (kloop g') (kloop g) ⟩
      kloop g' ∙' kloop g    ∎

mult-hom : GroupHom (fst A) 
             (PathGroup ((KG1 → KG1) , Π-level (λ _ → klevel)) (λ x → x))
mult-hom = record {f = f; pres-ident = pres-ident; pres-comp = pres-comp}
  where
  f = λ g → λ= (mult-loop g)

  pres-ident = 
    ap λ= (λ= (KG1-elim 
      {C = λ x → (mult-loop ident x == app= (idp {a = idf _}) x) , 
                 (=-preserves-level _ (=-preserves-level _ klevel))}
      (kloop-ident ∙ ! (ap-idf idp)) 
      (λ _ → prop-has-all-paths-↓ (klevel _ _ _ _))
      (set-↓-has-all-paths-↓ (=-preserves-level _ (klevel _ _)))
      (λ _ _ → set-↓-has-all-paths-↓ (=-preserves-level _ (klevel _ _)))))
    ∙ ! (λ=-η idp)

  pres-comp = λ g₁ g₂ → 
    ap λ= (λ= (KG1-elim
      {C = λ x → (_ , =-preserves-level _ (=-preserves-level _ klevel))}
      (kloop-comp g₁ g₂)
      (λ _ → prop-has-all-paths-↓ (klevel _ _ _ _))
      (set-↓-has-all-paths-↓ (=-preserves-level _ (klevel _ _)))
      (λ _ _ → set-↓-has-all-paths-↓ (=-preserves-level _ (klevel _ _))))) 
    ∙ ! (∙-λ= _ _)

mult : KG1 → KG1 → KG1
mult = KG1-rec {C = (KG1 → KG1) , Π-level (λ _ → klevel)} (λ x → x) mult-hom

H-KG1 : HSpaceStructure KG1
H-KG1 = record { e = kbase; μ = mult; μe- = μe-; μ-e = μ-e}
  where
  μe- : (x : KG1) → mult kbase x == x
  μe- = KG1-elim 
    {C = λ x → (mult kbase x == x) , =-preserves-level ⟨ 1 ⟩ klevel}
    idp
    (λ g → ↓-app=idf-in $ ∙'-unit-l (kloop g) ∙ (! (ap-idf (kloop g))) 
                          ∙ ! (∙-unit-r (ap (mult kbase) (kloop g))))
    (set-↓-has-all-paths-↓ (klevel _ _))
    (λ _ _ → set-↓-has-all-paths-↓ (klevel _ _))

  μ-e : (x : KG1) → mult x kbase == x
  μ-e = KG1-elim
    {C = λ x → (mult x kbase == x) , =-preserves-level ⟨ 1 ⟩ klevel}
    idp
    (λ g → ↓-app=idf-in $ 
       idp ∙' kloop g 
         =⟨ ∙'-unit-l (kloop g) ⟩
       kloop g
         =⟨ ! (app=-β (mult-loop g) kbase) ⟩
       app= (λ= (mult-loop g)) kbase
         =⟨ ! (KG1Rec.kloop-β (λ x → x) mult-hom g) |in-ctx (λ w → app= w kbase) ⟩
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