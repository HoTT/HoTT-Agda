{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.CommutingSquare
open import lib.types.Paths
open import lib.types.Pushout
open import lib.types.Sigma
open import lib.types.Span

module lib.types.PushoutFmap where

module PushoutFmap {i₀ j₀ k₀ i₁ j₁ k₁} {span₀ : Span {i₀} {j₀} {k₀}}
  {span₁ : Span {i₁} {j₁} {k₁}} (span-map : SpanMap span₀ span₁) 
  = PushoutRec {d = span₀} {D = Pushout span₁}
    (left ∘ SpanMap.hA span-map) (right ∘ SpanMap.hB span-map)
    -- the following concatenation arrangement works well with [Susp-fmap].
    (λ c →  ( ap left (SpanMap.f-commutes span-map □$ c)
            ∙ glue (SpanMap.hC span-map c))
         ∙' ap right (! (SpanMap.g-commutes span-map □$ c)))

Pushout-fmap = PushoutFmap.f

module _ {i₀ j₀ k₀ i₁ j₁ k₁} {span₀ : Span {i₀} {j₀} {k₀}}
  {span₁ : Span {i₁} {j₁} {k₁}} (span-equiv : SpanEquiv span₀ span₁) where

  private
    module S₀ = Span span₀
    module S₁ = Span span₁
    span-to = fst span-equiv
    span-from = fst (SpanEquiv-inverse span-equiv)
    open SpanMap span-to
    module To = PushoutFmap span-to
    module From = PushoutFmap span-from
    span-ise = snd span-equiv
    module hA = is-equiv (fst span-ise)
    module hB = is-equiv (fst (snd span-ise))
    module hC = is-equiv (snd (snd span-ise))

    to = To.f
    from = From.f

    postulate
      -- TODO
      to-from : ∀ y → to (from y) == y
      from-to : ∀ x → from (to x) == x

  Pushout-emap : Pushout span₀ ≃ Pushout span₁
  Pushout-emap = equiv to from to-from from-to
{-
    to-from : ∀ y → to (from y) == y
    to-from = Pushout-elim
      (λ a → ap left (hA.g-f a))
      (λ b → ap left (hB.g-f b))
      (λ c → ↓-∘=idf-in' $ ! $
          ap (to ∘ from) (glue c) ∙ ap right (hB.g-f (S₁.g b))
          
          ap to (ap from (glue c)) ∙ ap right (hB.g-f (S₁.g b))

        -- ap (hA.g ∘ S₁.f) (! $ hC.f-g c) ∙ ap hA.g (! $ commutes f-commutes (hC.g c)) ∙ hA.g-f (S₀.f (hC.g c))

        ap to (ap left (commutes f-commutes⁻¹ c)
         ∙  glue (hC.g c)
         ∙' ap right (! (commutes g-commutes⁻¹ c)))
          ∙ ap right (hB.g-f (S₁.g b))

          ap left (hA.f-g a) ∙' glue c
-}


