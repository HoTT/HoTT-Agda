{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module stash.modalities.FiberOfWedgeToProduct
  {i j} (X : Ptd i) (Y : Ptd j) where

  private
    X⊙×Y = X ⊙× Y
    module WedgeToProduct = WedgeRec (_, pt Y) (pt X ,_) idp

  ∨-to-× : X ∨ Y → de⊙ X⊙×Y
  ∨-to-× = WedgeToProduct.f

  private
    module To (x : de⊙ X) (y : de⊙ Y) = WedgeElim
      {P = λ x∨y → ∨-to-× x∨y == (x , y) → (pt X == x) * (pt Y == y)}
      (λ x p → right (snd×= p)) (λ y p → left (fst×= p))
      (↓-app→cst-in λ {p} {p'} p-path →
        (! (glue (fst×= p , snd×= p))
         ∙ ap (left ∘ fst×=)
            ( ↓-app=cst-out' p-path
            ∙ ap (_∙' p') WedgeToProduct.glue-β
            ∙ ∙'-unit-l p')))

    to : ∀ x y → hfiber ∨-to-× (x , y) → (pt X == x) * (pt Y == y)
    to x y = uncurry (To.f x y)

    private
      from-glue-template : ∀ {x y} (x-path : pt X == x) (y-path : pt Y == y)
        → (winr y , pair×= x-path idp) == (winl x , pair×= idp y-path)
            :> hfiber ∨-to-× (x , y)
      from-glue-template idp idp = pair= (! wglue) $
        ↓-app=cst-in' $ ! $ ap-! ∨-to-× wglue ∙ ap ! WedgeToProduct.glue-β

    module From (x : de⊙ X) (y : de⊙ Y) = JoinRec
      {D = hfiber ∨-to-× (x , y)}
      (λ x-path → winr y , pair×= x-path idp)
      (λ y-path → winl x , pair×= idp y-path)
      (uncurry from-glue-template)

    from : ∀ x y → (pt X == x) * (pt Y == y) → hfiber ∨-to-× (x , y)
    from = From.f

  postulate
    from-to : ∀ x y w → from x y (to x y w) == w
    to-from : ∀ x y j → to x y (from x y j) == j

  fiber-thm : ∀ x y → hfiber ∨-to-× (x , y) ≃ (pt X == x) * (pt Y == y)
  fiber-thm x y = equiv (to x y) (from x y) (to-from x y) (from-to x y)

