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
    to-glue-template : ∀ {x y}
      {p : (pt X , pt Y) == (x , y)}
      {p' : (pt X , pt Y) == (x , y)}
      (p-path : p == p' [ (λ w → ∨-to-× w == (x , y)) ↓ wglue ])
      → right (snd×= p) == left (fst×= p') :> (pt X == x) * (pt Y == y)
    to-glue-template {p = p} {p' = idp} p-path =
         ! (glue (fst×= p , snd×= p))
      ∙' ap (left ∘ fst×=) (↓-app=cst-out' p-path ∙ WedgeToProduct.glue-β)

    module To (x : de⊙ X) (y : de⊙ Y) = WedgeElim
      {P = λ x∨y → ∨-to-× x∨y == (x , y) → (pt X == x) * (pt Y == y)}
      (λ x p → right (snd×= p)) (λ y p → left (fst×= p))
      (↓-app→cst-in to-glue-template)

    to : ∀ x y → hfiber ∨-to-× (x , y) → (pt X == x) * (pt Y == y)
    to x y = uncurry (To.f x y)

    private
      from-glue-template : ∀ {x y} (x-path : pt X == x) (y-path : pt Y == y)
        → (winr y , pair×= x-path idp) == (winl x , pair×= idp y-path)
            :> hfiber ∨-to-× (x , y)
      from-glue-template idp idp = ! $ pair= wglue $
        ↓-app=cst-in' (! WedgeToProduct.glue-β)

    module From (x : de⊙ X) (y : de⊙ Y) = JoinRec
      {D = hfiber ∨-to-× (x , y)}
      (λ x-path → winr y , pair×= x-path idp)
      (λ y-path → winl x , pair×= idp y-path)
      (uncurry from-glue-template)

    from : ∀ x y → (pt X == x) * (pt Y == y) → hfiber ∨-to-× (x , y)
    from = From.f

  abstract
    to-from-glue-template : ∀ {x y} (x-path : pt X == x) (y-path : pt Y == y)
      → ap left (fst×=-β x-path idp) == ap right (snd×=-β idp y-path)
          [ (λ j → to x y (from x y j) == j) ↓ glue (x-path , y-path) ]
    to-from-glue-template idp idp = ↓-∘=idf-in' (to _ _) (from _ _) $
        ap (ap (to _ _)) (From.glue-β _ _ (idp , idp))
      ∙ ap-! (to _ _) (pair= wglue (↓-app=cst-in' (! WedgeToProduct.glue-β)))
      ∙ ap ! ( split-ap2 (to _ _) wglue (↓-app=cst-in' (! WedgeToProduct.glue-β))
             ∙ ap (λ p → ↓-app→cst-out p (↓-app=cst-in' (! WedgeToProduct.glue-β))) (To.glue-β _ _)
             ∙ ↓-app→cst-β to-glue-template (↓-app=cst-in' (! WedgeToProduct.glue-β))
             ∙ ap (λ p → ! (glue (idp , idp)) ∙' ap (left ∘ fst×=) p)
                 ( ap (_∙ WedgeToProduct.glue-β) (↓-app=cst-β' {p = wglue} (! WedgeToProduct.glue-β))
                 ∙ !-inv-l WedgeToProduct.glue-β))
      ∙ !-! (glue (idp , idp))

    to-from : ∀ x y j → to x y (from x y j) == j
    to-from x y = Join-elim
      {P = λ j → to x y (from x y j) == j}
      (λ x-path → ap left (fst×=-β x-path idp))
      (λ y-path → ap right (snd×=-β idp y-path))
      (uncurry to-from-glue-template)

  postulate
    from-to : ∀ x y w → from x y (to x y w) == w

  fiber-thm : ∀ x y → hfiber ∨-to-× (x , y) ≃ (pt X == x) * (pt Y == y)
  fiber-thm x y = equiv (to x y) (from x y) (to-from x y) (from-to x y)
