{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module cw.cohomology.grid.Map {i j k}
  {A : Type i} {B : Type j} {C : Type k}
  (f : A → B) (g : B → C) where

  B/A = Cofiber f
  C/A = Cofiber (g ∘ f)
  C/B = Cofiber g

  B/A-to-C/A-span-map : SpanMap (cofiber-span f) (cofiber-span (g ∘ f))
  B/A-to-C/A-span-map = span-map (idf _) g (idf _)
    (comm-sqr λ _ → idp) (comm-sqr λ _ → idp)
  module B/AToC/A = PushoutFmap B/A-to-C/A-span-map
  B/A-to-C/A : B/A → C/A
  B/A-to-C/A = B/AToC/A.f

  C/A-to-C/B-span-map : SpanMap (cofiber-span (g ∘ f)) (cofiber-span g)
  C/A-to-C/B-span-map = span-map (idf _) (idf _) f
    (comm-sqr λ _ → idp) (comm-sqr λ _ → idp)
  module C/AToC/B = PushoutFmap C/A-to-C/B-span-map
  C/A-to-C/B : C/A → C/B
  C/A-to-C/B = C/AToC/B.f
