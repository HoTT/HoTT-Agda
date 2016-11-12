{-# OPTIONS --without-K --rewriting #-}

open import HoTT

{- Proof that if [A] and [B] are two propositions, then so is [A * B]. -}

module homotopy.PropJoinProp
  {i} {A : Type i} (pA : is-prop A)
  {j} {B : Type j} (pB : is-prop B) where

contr-left : (a : A) → is-contr (A * B)
contr-left a = left a , Pushout-elim
  (λ a' → ap left (prop-has-all-paths pA a a'))
  (λ b' → glue (a , b'))
  (λ {(a' , b') → ↓-cst=idf-in' $ ! $
    ↓-app=cst-out (apd (λ a → glue (a , b')) (prop-has-all-paths pA a a'))})

contr-right : (b : B) → is-contr (A * B)
contr-right b = right b , Pushout-elim
  (λ a' → ! (glue (a' , b)))
  (λ b' → ap right (prop-has-all-paths pB b b'))
  (λ {(a' , b') → ↓-cst=idf-in' $
    ! (glue (a' , b)) ∙ glue (a' , b')
      =⟨ ! (↓-cst=app-out' $ apd (λ b → glue (a' , b)) (prop-has-all-paths pB b b'))
        |in-ctx ! (glue (a' , b)) ∙_ ⟩
    ! (glue (a' , b)) ∙ glue (a' , b) ∙ ap right (prop-has-all-paths pB b b')
      =⟨ ! $ ∙-assoc (! (glue (a' , b))) (glue (a' , b)) (ap right (prop-has-all-paths pB b b')) ⟩
    (! (glue (a' , b)) ∙ glue (a' , b)) ∙ ap right (prop-has-all-paths pB b b')
      =⟨ !-inv-l (glue (a' , b)) |in-ctx _∙ ap right (prop-has-all-paths pB b b') ⟩
    ap right (prop-has-all-paths pB b b')
      =∎})

prop*prop-is-prop : is-prop (A * B)
prop*prop-is-prop = inhab-to-contr-is-prop $
  Pushout-rec contr-left contr-right (λ _ → prop-has-all-paths is-contr-is-prop _ _)
