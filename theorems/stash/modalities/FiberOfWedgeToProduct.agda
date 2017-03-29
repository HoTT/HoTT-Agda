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
    ap-idf×cst : ∀ {x₀ x₁} (x= : x₀ == x₁)
      → ap (∨-to-× ∘ winl) x= == pair×= x= idp
    ap-idf×cst idp = idp

    ap-cst×idf : ∀ {y₀ y₁} (y= : y₀ == y₁)
      → ap (∨-to-× ∘ winr) y= == pair×= idp y=
    ap-cst×idf idp = idp

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

    module From = JoinRec
      {D = hfiber ∨-to-× (pt X⊙×Y)}
      (λ x-loop → winl (pt X) , pair×= x-loop idp)
      (λ y-loop → winr (pt Y) , pair×= idp y-loop)
      (λ{(x-loop , y-loop) → pair= ((ap winl x-loop ∙' wglue) ∙' ! (ap winr y-loop))
        $ ↓-app=cst-in' $ ! $
          ap ∨-to-× ((ap winl x-loop ∙' wglue) ∙' ! (ap winr y-loop)) ∙' pair×= idp y-loop
            =⟨ ap-∙' ∨-to-× (ap winl x-loop ∙' wglue) (! (ap winr y-loop)) |in-ctx _∙' pair×= idp y-loop ⟩
          (ap ∨-to-× (ap winl x-loop ∙' wglue) ∙' ap ∨-to-× (! (ap winr y-loop))) ∙' pair×= idp y-loop
            =⟨ ap2 _∙'_ (ap-∙' ∨-to-× (ap winl x-loop) wglue) (ap-! ∨-to-× (ap winr y-loop)) |in-ctx _∙' pair×= idp y-loop ⟩
          ((ap ∨-to-× (ap winl x-loop) ∙' ap ∨-to-× wglue) ∙' ! (ap ∨-to-× (ap winr y-loop))) ∙' pair×= idp y-loop
            =⟨ ap3 (λ p₀ p₁ p₂ → (p₀ ∙' p₁) ∙' ! p₂)
                (∘-ap ∨-to-× winl x-loop ∙' ap-idf×cst x-loop)
                WedgeToProduct.glue-β
                (∘-ap ∨-to-× winr y-loop ∙' ap-cst×idf y-loop)
                |in-ctx _∙' pair×= idp y-loop ⟩
          (pair×= x-loop idp ∙' ! (pair×= idp y-loop)) ∙' pair×= idp y-loop
            =⟨ ∙'-assoc (pair×= x-loop idp) (! (pair×= idp y-loop)) (pair×= idp y-loop) ⟩
          pair×= x-loop idp ∙' ! (pair×= idp y-loop) ∙' pair×= idp y-loop
            =⟨ ap (pair×= x-loop idp ∙'_) (!-inv'-l (pair×= idp y-loop)) ⟩
          pair×= x-loop idp
            =∎})

    from : (pt X == pt X) * (pt Y == pt Y) → hfiber ∨-to-× (pt X⊙×Y)
    from = From.f
