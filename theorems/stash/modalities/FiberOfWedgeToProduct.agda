{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module stash.modalities.FiberOfWedgeToProduct
  {i j} (X : Ptd i) (Y : Ptd j) where

  private
    X⊙×Y = X ⊙× Y
    module WedgeToProduct = WedgeRec (_, pt Y) (pt X ,_) idp

  ∨-to-× : X ∨ Y → de⊙ X⊙×Y
  ∨-to-× = WedgeToProduct.f

  ∨-to-×-glue-β : ap ∨-to-× wglue == idp
  ∨-to-×-glue-β = WedgeToProduct.glue-β 

  private
    module To = WedgeElim
      {P = λ x∨y → ∨-to-× x∨y == pt X⊙×Y → (pt X == pt X) * (pt Y == pt Y)}
      (λ x p → right (snd×= p)) (λ y p → left (fst×= p))
      (↓-app→cst-in λ {p} {p'} p= →
        (! (glue (fst×= p , snd×= p))
         ∙ ap (left ∘ fst×=)
            ( ↓-app=cst-out p=
            ∙ ap (_∙ p') WedgeToProduct.glue-β)))

    to : hfiber ∨-to-× (pt X⊙×Y) → (pt X == pt X) * (pt Y == pt Y)
    to = uncurry To.f

    private
      from-glue : ∀ {x y} (x-path : x == pt X) (y-path : y == pt Y)
        → (winl x , pair×= x-path idp) == (winr y , pair×= idp y-path)
            :> hfiber ∨-to-× (pt X⊙×Y)
      from-glue idp idp = pair= wglue (↓-app=cst-in' (! WedgeToProduct.glue-β))

    module From = JoinRec
      {D = hfiber ∨-to-× (pt X⊙×Y)}
      (λ x-loop → winl (pt X) , pair×= x-loop idp)
      (λ y-loop → winr (pt Y) , pair×= idp y-loop)
      (uncurry from-glue)

    from : (pt X == pt X) * (pt Y == pt Y) → hfiber ∨-to-× (pt X⊙×Y)
    from = From.f

  postulate
    fiber-thm : (x : de⊙ X) (y : de⊙ Y) → hfiber ∨-to-× (x , y) ≃ (pt X == x) * (pt Y == y)

