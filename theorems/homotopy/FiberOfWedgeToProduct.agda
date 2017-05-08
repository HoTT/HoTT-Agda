{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.FiberOfWedgeToProduct {i j} (X : Ptd i) (Y : Ptd j) where

  private
    X⊙×Y = X ⊙× Y

  private
    to-glue-template : ∀ {x y}
      {p p' : (pt X , pt Y) == (x , y)}
      (q : p == p' [ (λ w → ∨-to-× w == (x , y)) ↓ wglue ])
      → right (snd×= p) == left (fst×= p') :> (pt X == x) * (pt Y == y)
    to-glue-template {p = p} {p' = p'} q =
      ! (glue (fst×= p , snd×= p)) ∙' ap (left ∘ fst×=) (↓-∨to×=cst-out q)

    module To (x : de⊙ X) (y : de⊙ Y) = WedgeElim
      {P = λ x∨y → ∨-to-× x∨y == (x , y) → (pt X == x) * (pt Y == y)}
      (λ x p → right (snd×= p)) (λ y p → left (fst×= p))
      (↓-app→cst-in to-glue-template)

  to : ∀ x y → hfiber ∨-to-× (x , y) → (pt X == x) * (pt Y == y)
  to x y = uncurry (To.f x y)

  private
    -- the only needed β-rule for [to] applied to [wglue].
    abstract
      to-glue-idp-β : ap (to (pt X) (pt Y)) (pair= wglue (↓-∨to×=cst-in idp))
        == ! (glue (idp , idp))
      to-glue-idp-β =
          split-ap2 (to _ _) wglue (↓-∨to×=cst-in idp)
        ∙ ap (λ p → ↓-app→cst-out p (↓-∨to×=cst-in idp)) (To.glue-β _ _)
        ∙ ↓-app→cst-β to-glue-template (↓-∨to×=cst-in idp)
        ∙ ap (λ p → ! (glue (idp , idp)) ∙' ap (left ∘ fst×=) p) (↓-∨to×=cst-β idp)

  private
    from-glue-template : ∀ {x y} (x-path : pt X == x) (y-path : pt Y == y)
      → (winr y , pair×= x-path idp) == (winl x , pair×= idp y-path)
          :> hfiber ∨-to-× (x , y)
    from-glue-template idp idp = ! $ pair= wglue (↓-∨to×=cst-in idp)

    module From (x : de⊙ X) (y : de⊙ Y) = JoinRec
      {D = hfiber ∨-to-× (x , y)}
      (λ x-path → winr y , pair×= x-path idp)
      (λ y-path → winl x , pair×= idp y-path)
      (uncurry from-glue-template)

  from : ∀ x y → (pt X == x) * (pt Y == y) → hfiber ∨-to-× (x , y)
  from = From.f

  private
    abstract
      to-from-glue-template : ∀ {x y} (x-path : pt X == x) (y-path : pt Y == y)
        → ap left (fst×=-β x-path idp) == ap right (snd×=-β idp y-path)
            [ (λ j → to x y (from x y j) == j) ↓ glue (x-path , y-path) ]
      to-from-glue-template idp idp = ↓-∘=idf-in' (to _ _) (from _ _) $
          ap (ap (to _ _)) (From.glue-β _ _ (idp , idp))
        ∙ ap-! (to _ _) (pair= wglue (↓-∨to×=cst-in idp))
        ∙ ap ! to-glue-idp-β
        ∙ !-! (glue (idp , idp))

    to-from : ∀ x y j → to x y (from x y j) == j
    to-from x y = Join-elim
      {P = λ j → to x y (from x y j) == j}
      (λ x-path → ap left (fst×=-β x-path idp))
      (λ y-path → ap right (snd×=-β idp y-path))
      (uncurry to-from-glue-template)

  private
    abstract
      from-to-winl-template : ∀ {x x' y} (xy-path : (x' , pt Y) == (x , y))
        → (winl x , pair×= idp (snd×= xy-path)) == (winl x' , xy-path)
            :> hfiber (∨-to-× {X = X} {Y = Y}) (x , y)
      from-to-winl-template idp = idp

      from-to-winr-template : ∀ {x y y'} (xy-path : (pt X , y') == (x , y))
        → (winr y , pair×= (fst×= xy-path) idp) == (winr y' , xy-path)
            :> hfiber (∨-to-× {X = X} {Y = Y}) (x , y)
      from-to-winr-template idp = idp

      -- this version enables path induction on [q] which
      -- turns *both* [p] and [p'] into [idp]. yay!
      from-to-glue-template' : ∀ {x y}
        (p p' : (pt X , pt Y) == (x , y)) (q : p == p')
        → from-to-winl-template p == from-to-winr-template p'
          [ (λ xy → from x y (to x y xy) == xy) ↓ pair= wglue (↓-∨to×=cst-in q) ]
      from-to-glue-template' idp .idp idp =
        ↓-∘=idf-in' (from (pt X) (pt Y)) (to (pt X) (pt Y)) $
            ap (ap (from _ _)) to-glue-idp-β
          ∙ ap-! (from _ _) (glue (idp , idp))
          ∙ ap ! (From.glue-β _ _ (idp , idp))
          ∙ !-! (pair= wglue (↓-∨to×=cst-in idp))

      from-to-glue-template : ∀ {x y}
        (p p' : (pt X , pt Y) == (x , y))
        (q : p == p' [ (λ w → ∨-to-× w == (x , y)) ↓ wglue ])
        → from-to-winl-template p == from-to-winr-template p'
          [ (λ xy → from x y (to x y xy) == xy) ↓ pair= wglue q ]
      from-to-glue-template {x} {y} p p' q =
        transport
          (λ q →
            from-to-winl-template p == from-to-winr-template p'
            [ (λ xy → from x y (to x y xy) == xy) ↓ pair= wglue q ])
          (↓-∨to×=cst-η q) 
          (from-to-glue-template' p p' (↓-∨to×=cst-out q))

    from-to : ∀ x y hf → from x y (to x y hf) == hf
    from-to x y = uncurry $ Wedge-elim
      {P = λ w → ∀ p → from x y (To.f x y w p) == (w , p)}
      (λ x → from-to-winl-template)
      (λ y → from-to-winr-template)
      (↓-Π-in λ {p} {p'} → from-to-glue-template p p')

  fiber-thm : ∀ x y → hfiber ∨-to-× (x , y) ≃ (pt X == x) * (pt Y == y)
  fiber-thm x y = equiv (to x y) (from x y) (to-from x y) (from-to x y)
