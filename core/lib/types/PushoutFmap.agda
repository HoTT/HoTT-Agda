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

Pushout-fmap-∘ : ∀ {i₀ j₀ k₀ i₁ j₁ k₁ i₂ j₂ k₂} {span₀ : Span {i₀} {j₀} {k₀}}
  {span₁ : Span {i₁} {j₁} {k₁}} {span₂ : Span {i₂} {j₂} {k₂}}
  (span-map₁₂ : SpanMap span₁ span₂) (span-map₀₁ : SpanMap span₀ span₁)
  → ∀ p → Pushout-fmap (SpanMap-∘ span-map₁₂ span-map₀₁) p
       == Pushout-fmap span-map₁₂ (Pushout-fmap span-map₀₁ p)
Pushout-fmap-∘ span-map₁₂ span-map₀₁
  = Pushout-elim (λ _ → idp) (λ _ → idp)
      (λ c → ↓-='-in' $
        ap (Pushout-fmap span-map₁₂ ∘ Pushout-fmap span-map₀₁) (glue c)
          =⟨ ap-∘ (Pushout-fmap span-map₁₂) (Pushout-fmap span-map₀₁) (glue c) ⟩
        ap (Pushout-fmap span-map₁₂) (ap (Pushout-fmap span-map₀₁) (glue c))
          =⟨ PushoutFmap.glue-β span-map₀₁ c |in-ctx ap (Pushout-fmap span-map₁₂) ⟩
        ap (Pushout-fmap span-map₁₂)
          ( ( ap left (span-map₀₁.f-commutes □$ c)
              ∙ glue (span-map₀₁.hC c))
            ∙' ap right (! (span-map₀₁.g-commutes □$ c)))
          =⟨ ap-∙' (Pushout-fmap span-map₁₂)
              (ap left (span-map₀₁.f-commutes □$ c) ∙ glue (span-map₀₁.hC c))
              (ap right (! (span-map₀₁.g-commutes □$ c))) ⟩
        ap (Pushout-fmap span-map₁₂) ( ap left (span-map₀₁.f-commutes □$ c)
                                       ∙ glue (span-map₀₁.hC c))
        ∙' ap (Pushout-fmap span-map₁₂) (ap right (! (span-map₀₁.g-commutes □$ c)))
          =⟨ ap2 _∙'_ (ap-∙ (Pushout-fmap span-map₁₂)
                        (ap left (span-map₀₁.f-commutes □$ c))
                        (glue (span-map₀₁.hC c)))
                      (∘-ap (Pushout-fmap span-map₁₂) right (! (span-map₀₁.g-commutes □$ c))) ⟩
        ( ap (Pushout-fmap span-map₁₂) (ap left (span-map₀₁.f-commutes □$ c))
          ∙ ap (Pushout-fmap span-map₁₂) (glue (span-map₀₁.hC c)))
        ∙' ap (right ∘ span-map₁₂.hB) (! (span-map₀₁.g-commutes □$ c))
          =⟨ ap2 _∙'_
              -- favonia: for some reasons Agda seems to need this.
              {x = ap (Pushout-fmap span-map₁₂) (ap left (span-map₀₁.f-commutes □$ c))
                 ∙ ap (Pushout-fmap span-map₁₂) (glue (span-map₀₁.hC c))}
              (ap2 _∙_
                (∘-ap (Pushout-fmap span-map₁₂) left (span-map₀₁.f-commutes □$ c))
                (PushoutFmap.glue-β span-map₁₂ (span-map₀₁.hC c)))
              (ap-∘ right span-map₁₂.hB (! (span-map₀₁.g-commutes □$ c))) ⟩
        ( ap (left ∘ span-map₁₂.hA) (span-map₀₁.f-commutes □$ c)
          ∙ ( ( ap left (span-map₁₂.f-commutes □$ span-map₀₁.hC c)
              ∙ glue (span-map₁₂.hC (span-map₀₁.hC c)))
            ∙' ap right (! (span-map₁₂.g-commutes □$ span-map₀₁.hC c))))
        ∙' ap right (ap span-map₁₂.hB (! (span-map₀₁.g-commutes □$ c)))
          =⟨ ap-mega-assoc
              (ap (left ∘ span-map₁₂.hA) (span-map₀₁.f-commutes □$ c))
              (ap left (span-map₁₂.f-commutes □$ span-map₀₁.hC c))
              (glue (span-map₁₂.hC (span-map₀₁.hC c)))
              (ap right (! (span-map₁₂.g-commutes □$ span-map₀₁.hC c)))
              (ap right (ap span-map₁₂.hB (! (span-map₀₁.g-commutes □$ c)))) ⟩
        ( ( ap (left ∘ span-map₁₂.hA) (span-map₀₁.f-commutes □$ c)
            ∙ ap left (span-map₁₂.f-commutes □$ span-map₀₁.hC c))
          ∙ glue (span-map₁₂.hC (span-map₀₁.hC c)))
        ∙'( ap right (! (span-map₁₂.g-commutes □$ span-map₀₁.hC c))
            ∙ ap right (ap span-map₁₂.hB (! (span-map₀₁.g-commutes □$ c))))
          =⟨ ap2 _∙'_
              ( ap-∘ left span-map₁₂.hA (span-map₀₁.f-commutes □$ c)
                |in-ctx _∙ ap left (span-map₁₂.f-commutes □$ span-map₀₁.hC c)
                |in-ctx _∙ glue (span-map₁₂.hC (span-map₀₁.hC c)))
              ( ∙-ap right
                  (! (span-map₁₂.g-commutes □$ span-map₀₁.hC c))
                  (ap span-map₁₂.hB (! (span-map₀₁.g-commutes □$ c)))) ⟩
        ( ( ap left (ap span-map₁₂.hA (span-map₀₁.f-commutes □$ c))
            ∙ ap left (span-map₁₂.f-commutes □$ span-map₀₁.hC c))
          ∙ glue (span-map₁₂.hC (span-map₀₁.hC c)))
        ∙' ap right
             ( ! (span-map₁₂.g-commutes □$ span-map₀₁.hC c)
               ∙ ap span-map₁₂.hB (! (span-map₀₁.g-commutes □$ c)))
          =⟨ ap2 _∙'_
              ( ∙-ap left
                  (ap span-map₁₂.hA (span-map₀₁.f-commutes □$ c))
                  (span-map₁₂.f-commutes □$ span-map₀₁.hC c)
                |in-ctx _∙ glue (span-map₁₂.hC (span-map₀₁.hC c)))
              ( ap-! span-map₁₂.hB (span-map₀₁.g-commutes □$ c)
                |in-ctx ! (span-map₁₂.g-commutes □$ span-map₀₁.hC c) ∙_
                |in-ctx ap right) ⟩
        ( ap left (CommSquare-∘v span-map₁₂.f-commutes span-map₀₁.f-commutes □$ c)
          ∙ glue (span-map₁₂.hC (span-map₀₁.hC c)))
        ∙' ap right
             ( ! (span-map₁₂.g-commutes □$ span-map₀₁.hC c)
               ∙ ! (ap span-map₁₂.hB (span-map₀₁.g-commutes □$ c)))
          =⟨ ∙-!
               (span-map₁₂.g-commutes □$ span-map₀₁.hC c)
               (ap span-map₁₂.hB (span-map₀₁.g-commutes □$ c))
            |in-ctx ap right
            |in-ctx
              ( ap left (CommSquare-∘v span-map₁₂.f-commutes span-map₀₁.f-commutes □$ c)
                ∙ glue (span-map₁₂.hC (span-map₀₁.hC c)))
              ∙'_ ⟩
        ( ap left (CommSquare-∘v span-map₁₂.f-commutes span-map₀₁.f-commutes □$ c)
          ∙ glue (span-map₁₂.hC (span-map₀₁.hC c)))
        ∙' ap right (! (CommSquare-∘v span-map₁₂.g-commutes span-map₀₁.g-commutes □$ c))
          =⟨ ! (PushoutFmap.glue-β (SpanMap-∘ span-map₁₂ span-map₀₁) c) ⟩
        ap (Pushout-fmap (SpanMap-∘ span-map₁₂ span-map₀₁)) (glue c)
          =∎)
  where
    module span-map₀₁ = SpanMap span-map₀₁
    module span-map₁₂ = SpanMap span-map₁₂

    ap-mega-assoc : ∀ {i} {A : Type i} {a₀ a₁ a₂ a₃ a₄ a₅ : A}
      (p₀ : a₀ == a₁) (p₁ : a₁ == a₂) (p₂ : a₂ == a₃) (p₃ : a₃ == a₄) (p₄ : a₄ == a₅)
      → (p₀ ∙ ((p₁ ∙ p₂) ∙' p₃)) ∙' p₄ == ((p₀ ∙ p₁) ∙ p₂) ∙' (p₃ ∙ p₄)
    ap-mega-assoc idp p₁ p₂ idp p₄ = idp

module _ {i₀ j₀ k₀ i₁ j₁ k₁} {span₀ : Span {i₀} {j₀} {k₀}}
  {span₁ : Span {i₁} {j₁} {k₁}} (span-equiv : SpanEquiv span₀ span₁) where

  private
    module span₀ = Span span₀
    module span₁ = Span span₁
    span-to = fst span-equiv
    span-from = fst (SpanEquiv-inverse span-equiv)
    module span-to = SpanMap span-to
    module span-from = SpanMap span-from
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


