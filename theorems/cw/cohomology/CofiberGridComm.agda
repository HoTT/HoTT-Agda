{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.PushoutSplit

module cw.cohomology.CofiberGridComm {i j k l}
  {A : Type i} {B : Type j} {C : Type k} {D : Type l}
  (f : A → B) (g : B → C) (h : C → D) where

  C/A = Cofiber (g ∘ f)
  C/B = Cofiber g
  D/A = Cofiber (h ∘ g ∘ f)
  D/B = Cofiber (h ∘ g)

  private
    C/A-to-D/A-span-map : SpanMap (cofiber-span (g ∘ f)) (cofiber-span (h ∘ g ∘ f))
    C/A-to-D/A-span-map = span-map (idf _) h (idf _)
      (comm-sqr λ _ → idp) (comm-sqr λ _ → idp)
  C/A-to-D/A : C/A → D/A
  C/A-to-D/A = Pushout-fmap C/A-to-D/A-span-map

  private
    D/A-to-D/B-span-map : SpanMap (cofiber-span (h ∘ g ∘ f)) (cofiber-span (h ∘ g))
    D/A-to-D/B-span-map = span-map (idf _) (idf _) f
      (comm-sqr λ _ → idp) (comm-sqr λ _ → idp)
  D/A-to-D/B : D/A → D/B
  D/A-to-D/B = Pushout-fmap D/A-to-D/B-span-map

  private
    C/A-to-C/B-span-map : SpanMap (cofiber-span (g ∘ f)) (cofiber-span g)
    C/A-to-C/B-span-map = span-map (idf _) (idf _) f
      (comm-sqr λ _ → idp) (comm-sqr λ _ → idp)
  C/A-to-C/B : C/A → C/B
  C/A-to-C/B = Pushout-fmap C/A-to-C/B-span-map

  private
    C/B-to-D/B-span-map : SpanMap (cofiber-span g) (cofiber-span (h ∘ g))
    C/B-to-D/B-span-map = span-map (idf _) h (idf _)
      (comm-sqr λ _ → idp) (comm-sqr λ _ → idp)
  C/B-to-D/B : C/B → D/B
  C/B-to-D/B = Pushout-fmap C/B-to-D/B-span-map

  grid-commutes : ∀ c/a → D/A-to-D/B (C/A-to-D/A c/a) == C/B-to-D/B (C/A-to-C/B c/a)
  grid-commutes = Cofiber-elim idp (λ _ → idp)
    (λ a → ↓-='-in' $ ap-∘ C/B-to-D/B C/A-to-C/B (glue a)
                    ∙ ap (ap C/B-to-D/B) (PushoutFmap.glue-β C/A-to-C/B-span-map a)
                    ∙ PushoutFmap.glue-β C/B-to-D/B-span-map (f a)
                    ∙ ! (PushoutFmap.glue-β D/A-to-D/B-span-map a)
                    ∙ ap (ap D/A-to-D/B) (! (PushoutFmap.glue-β C/A-to-D/A-span-map a))
                    ∙ ∘-ap D/A-to-D/B C/A-to-D/A (glue a)))
