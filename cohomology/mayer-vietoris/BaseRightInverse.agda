{-# OPTIONS --without-K #-}

open import HoTT

module cohomology.mayer-vietoris.BaseRightInverse {i j k} {A : Type i}
  {B : Type j} (Z : Ptd k) (f : fst Z → A) (g : fst Z → B) where

open import cohomology.mayer-vietoris.BaseEquivMaps Z f g
open import cohomology.mayer-vietoris.Functions ps

private
  sq : (z : fst Z) →
    Square idp (ap into (ap out (merid _ z))) (merid _ z) (merid _ (snd Z))
  sq z =
    (ap (ap into) (Out.glue-β z) ∙v⊡
      (! (Into.glue-β (winl (f z)))) ∙h⊡
        ap-square into (out-square z)
      ⊡h∙ (Into.glue-β (winr (g z))))
    ⊡v∙ (∘-ap into (cfcod _) (glue z) ∙ IntoCod.glue-β z)

{- Right inverse -}
into-out : ∀ σ → into (out σ) == σ
into-out = Suspension-elim (fst Z)
  idp
  (merid _ (snd Z))
  (λ z → ↓-∘=idf-from-square into out (sq z))
