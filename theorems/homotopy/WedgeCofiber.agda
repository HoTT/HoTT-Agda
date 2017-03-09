{-# OPTIONS --without-K --rewriting #-}

open import HoTT

{- The cofiber space of [winl : X → X ∨ Y] is equivalent to [Y],
 - and the cofiber space of [winr : Y → X ∨ Y] is equivalent to [X]. -}

module homotopy.WedgeCofiber {i} (X Y : Ptd i) where

  module CofWinl where

    module Into = CofiberRec {f = winl} (pt Y) (projr X Y) (λ _ → idp)

    into = Into.f

    out : de⊙ Y → Cofiber (winl {X = X} {Y = Y})
    out = cfcod ∘ winr

    abstract
      out-into : (κ : Cofiber (winl {X = X} {Y = Y})) → out (into κ) == κ
      out-into = Cofiber-elim
        (! (cfglue (pt X) ∙ ap cfcod wglue))
        (Wedge-elim
          (λ x → ! (cfglue (pt X) ∙ ap cfcod wglue) ∙ cfglue x)
          (λ y → idp)
          (↓-='-from-square $
            (lemma (cfglue (pt X)) (ap cfcod wglue)
             ∙h⊡ (ap-∘ out (projr X Y) wglue ∙ ap (ap out) (Projr.glue-β X Y))
                  ∙v⊡ bl-square (ap cfcod wglue))))
        (λ x → ↓-∘=idf-from-square out into $
          ! (∙-unit-r _) ∙h⊡
            ap (ap out) (Into.glue-β x) ∙v⊡
             hid-square {p = (! (cfglue' winl (pt X) ∙ ap cfcod wglue))}
             ⊡v connection {q = cfglue x})
        where
        lemma : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : y == z)
          → ! (p ∙ q) ∙ p == ! q
        lemma idp idp = idp

    eq : Cofiber winl ≃ de⊙ Y
    eq = equiv into out (λ _ → idp) out-into

    ⊙eq : ⊙Cofiber ⊙winl ⊙≃ Y
    ⊙eq = ≃-to-⊙≃ eq idp

  cfcod-winl-projr-comm-sqr : CommSquare (cfcod' winl) (projr X Y) (idf _) CofWinl.into
  cfcod-winl-projr-comm-sqr = comm-sqr λ _ → idp

  module CofWinr where

    module Into = CofiberRec {f = winr} (pt X) (projl X Y) (λ _ → idp)

    into = Into.f

    out : de⊙ X → Cofiber (winr {X = X} {Y = Y})
    out = cfcod ∘ winl

    abstract
      out-into : ∀ κ → out (into κ) == κ
      out-into = Cofiber-elim
        (ap cfcod wglue ∙ ! (cfglue (pt Y)))
        (Wedge-elim
          (λ x → idp)
          (λ y → (ap cfcod wglue ∙ ! (cfglue (pt Y))) ∙ cfglue y)
          (↓-='-from-square $
            (ap-∘ out (projl X Y) wglue ∙ ap (ap out) (Projl.glue-β X Y)) ∙v⊡
               connection
             ⊡h∙ ! (lemma (ap (cfcod' winr) wglue) (cfglue (pt Y)))))
        (λ y → ↓-∘=idf-from-square out into $
          ! (∙-unit-r _) ∙h⊡
            ap (ap out) (Into.glue-β y) ∙v⊡
              hid-square {p = (ap (cfcod' winr) wglue ∙ ! (cfglue (pt Y)))}
              ⊡v connection {q = cfglue y})
        where
        lemma : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : z == y)
          → (p ∙ ! q) ∙ q == p
        lemma idp idp = idp

    eq : Cofiber winr ≃ de⊙ X
    eq = equiv into out (λ _ → idp) out-into

    ⊙eq : ⊙Cofiber ⊙winr ⊙≃ X
    ⊙eq = ≃-to-⊙≃ eq idp

  cfcod-winr-projl-comm-sqr : CommSquare (cfcod' winr) (projl X Y) (idf _) CofWinr.into
  cfcod-winr-projl-comm-sqr = comm-sqr λ _ → idp
