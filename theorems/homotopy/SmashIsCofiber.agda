{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.elims.CofPushoutSection as CofPushoutSection

module homotopy.SmashIsCofiber {i j} (X : Ptd i) (Y : Ptd j) where

{- the proof that our smash matches the more classical definition as a cofiber -}

Smash-equiv-Cof : Smash X Y ≃ Cofiber (∨-to-× {X = X} {Y = Y})
Smash-equiv-Cof = equiv to from to-from from-to where
  module To = SmashRec {C = Cofiber (∨-to-× {X = X} {Y = Y})}
    cfbase cfbase (curry cfcod)
    (λ x → cfglue (winl x)) (λ y → cfglue (winr y))
  to : Smash X Y → Cofiber (∨-to-× {X = X} {Y = Y})
  to = To.f

  module FromGlue = WedgeElim
    {P = λ x∨y → smin (pt X) (pt Y) == uncurry smin (∨-to-× {X = X} {Y = Y} x∨y)}
    (λ x → ! (smgluel (pt X)) ∙ smgluel x)
    (λ y → ! (smgluer (pt Y)) ∙ smgluer y)
    (↓-cst=app-in $
        ap2 _∙'_ (!-inv-l (smgluel (pt X)))
          ( ap-∘ (uncurry smin) (∨-to-× {X = X} {Y = Y}) wglue
          ∙ ap (ap (uncurry smin)) (∨-to-×-glue-β {X = X} {Y = Y}))
      ∙ ! (!-inv-l (smgluer (pt Y))))

  module From = CofiberRec {C = Smash X Y}
    (smin (pt X) (pt Y)) (uncurry smin)
    FromGlue.f

  from : Cofiber (∨-to-× {X = X} {Y = Y}) → Smash X Y
  from = From.f

  abstract
    from-to : ∀ x → from (to x) == x
    from-to = Smash-elim (! (smgluel (pt X))) (! (smgluer (pt Y))) (λ _ _ → idp)
      (λ x → ↓-∘=idf-in' from to $
        ap from (ap to (smgluel x))
          =⟨ ap (ap from) (To.smgluel-β x) ⟩
        ap from (cfglue (winl x))
          =⟨ From.glue-β (winl x) ⟩
        ! (smgluel (pt X)) ∙ smgluel x
          =∎)
      (λ y → ↓-∘=idf-in' from to $
        ap from (ap to (smgluer y))
          =⟨ ap (ap from) (To.smgluer-β y) ⟩
        ap from (cfglue (winr y))
          =⟨ From.glue-β (winr y) ⟩
        ! (smgluer (pt Y)) ∙ smgluer y
          =∎)

    to-from : ∀ x → to (from x) == x
    to-from = CofPushoutSection.elim
      (λ _ → unit) (λ _ → idp)
      (! (cfglue (winr (pt Y)))) (λ _ → idp)
      (λ x → ↓-∘=idf-in' to from $
        ap to (ap from (cfglue (winl x)))
          =⟨ ap (ap to) (From.glue-β (winl x)) ⟩
        ap to (FromGlue.f (winl x))
          =⟨ ap-∙ to (! (smgluel (pt X))) (smgluel x) ⟩
        ap to (! (smgluel (pt X))) ∙ ap to (smgluel x)
          =⟨ ap2 _∙_
              (ap-! to (smgluel (pt X)) ∙ ap ! (To.smgluel-β (pt X)))
              (To.smgluel-β x) ⟩
        ! (cfglue (winl (pt X))) ∙ cfglue (winl x)
          =⟨ ap (λ p → ! p ∙ cfglue (winl x)) $
              ap (cfglue (winl (pt X)) ∙'_)
                ( ap (ap cfcod) (! ∨-to-×-glue-β)
                ∙ ∘-ap cfcod ∨-to-× wglue)
            ∙ ↓-cst=app-out (apd cfglue wglue)
          ⟩
        ! (cfglue (winr (pt Y))) ∙ cfglue (winl x)
          =∎)
      (λ y → ↓-∘=idf-in' to from $
        ap to (ap from (cfglue (winr y)))
          =⟨ ap (ap to) (From.glue-β (winr y)) ⟩
        ap to (FromGlue.f (winr y))
          =⟨ ap-∙ to (! (smgluer (pt Y))) (smgluer y) ⟩
        ap to (! (smgluer (pt Y))) ∙ ap to (smgluer y)
          =⟨ ap2 _∙_
              (ap-! to (smgluer (pt Y)) ∙ ap ! (To.smgluer-β (pt Y)))
              (To.smgluer-β y) ⟩
        ! (cfglue (winr (pt Y))) ∙ cfglue (winr y)
          =∎)

Smash-⊙equiv-Cof : ⊙Smash X Y ⊙≃ ⊙Cofiber (∨-⊙to-× {X = X} {Y = Y})
Smash-⊙equiv-Cof = ≃-to-⊙≃ Smash-equiv-Cof idp
