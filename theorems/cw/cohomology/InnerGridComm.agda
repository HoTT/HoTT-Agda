{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Theory

module cw.cohomology.InnerGridComm {i} (OT : OrdinaryTheory i)
  (n : ℤ) {X Y Z W : Ptd i} (f : X ⊙→ Y) (g : Y ⊙→ Z) (h : Z ⊙→ W) where

  open OrdinaryTheory OT
  open import cohomology.PtdMapSequence cohomology-theory

  Z/X = ⊙Cofiber (g ⊙∘ f)
  Z/Y = ⊙Cofiber g
  W/X = ⊙Cofiber (h ⊙∘ g ⊙∘ f)
  W/Y = ⊙Cofiber (h ⊙∘ g)

  private
    Z/X-to-W/X-span-map : SpanMap (cofiber-span (fst g ∘ fst f)) (cofiber-span (fst h ∘ fst g ∘ fst f))
    Z/X-to-W/X-span-map = span-map (idf _) (fst h) (idf _)
      (comm-sqr λ _ → idp) (comm-sqr λ _ → idp)
  Z/X-to-W/X : Z/X ⊙→ W/X
  Z/X-to-W/X = Pushout-fmap Z/X-to-W/X-span-map , idp

  private
    W/X-to-W/Y-span-map : SpanMap (cofiber-span (fst h ∘ fst g ∘ fst f)) (cofiber-span (fst h ∘ fst g))
    W/X-to-W/Y-span-map = span-map (idf _) (idf _) (fst f)
      (comm-sqr λ _ → idp) (comm-sqr λ _ → idp)
  W/X-to-W/Y : W/X ⊙→ W/Y
  W/X-to-W/Y = Pushout-fmap W/X-to-W/Y-span-map , idp

  private
    Z/X-to-Z/Y-span-map : SpanMap (cofiber-span (fst g ∘ fst f)) (cofiber-span (fst g))
    Z/X-to-Z/Y-span-map = span-map (idf _) (idf _) (fst f)
      (comm-sqr λ _ → idp) (comm-sqr λ _ → idp)
  Z/X-to-Z/Y : Z/X ⊙→ Z/Y
  Z/X-to-Z/Y = Pushout-fmap Z/X-to-Z/Y-span-map , idp

  private
    Z/Y-to-W/Y-span-map : SpanMap (cofiber-span (fst g)) (cofiber-span (fst h ∘ fst g))
    Z/Y-to-W/Y-span-map = span-map (idf _) (fst h) (idf _)
      (comm-sqr λ _ → idp) (comm-sqr λ _ → idp)
  Z/Y-to-W/Y : Z/Y ⊙→ W/Y
  Z/Y-to-W/Y = Pushout-fmap Z/Y-to-W/Y-span-map , idp

  grid-comm-sqr : CommSquare (fst Z/X-to-W/X) (fst Z/Y-to-W/Y) (fst Z/X-to-Z/Y) (fst W/X-to-W/Y)
  grid-comm-sqr = comm-sqr $ Cofiber-elim idp (λ _ → idp)
    (λ a → ↓-='-in' $ ap-∘ (fst Z/Y-to-W/Y) (fst Z/X-to-Z/Y) (glue a)
                    ∙ ap (ap (fst Z/Y-to-W/Y)) (PushoutFmap.glue-β Z/X-to-Z/Y-span-map a)
                    ∙ PushoutFmap.glue-β Z/Y-to-W/Y-span-map ((fst f) a)
                    ∙ ! (PushoutFmap.glue-β W/X-to-W/Y-span-map a)
                    ∙ ap (ap (fst W/X-to-W/Y)) (! (PushoutFmap.glue-β Z/X-to-W/X-span-map a))
                    ∙ ∘-ap (fst W/X-to-W/Y) (fst Z/X-to-W/X) (glue a))

  C-grid-commutes : CommSquareᴳ
    (C-fmap n Z/Y-to-W/Y) (C-fmap n Z/X-to-W/X) (C-fmap n W/X-to-W/Y) (C-fmap n Z/X-to-Z/Y)
  C-grid-commutes = C-comm-square n grid-comm-sqr
