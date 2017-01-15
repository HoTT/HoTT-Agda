{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.cubical.Square
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
Pushout-fmap-∘ {span₀ = span₀} {span₁} span-map₁₂ span-map₀₁
  = Pushout-elim (λ _ → idp) (λ _ → idp) lemma
  where
    module span-map₀₁ = SpanMap span-map₀₁
    module span-map₁₂ = SpanMap span-map₁₂
    ap-mega-assoc : ∀ {i} {A : Type i} {a₀ a₁ a₂ a₃ a₄ a₅ : A}
      (p₀ : a₀ == a₁) (p₁ : a₁ == a₂) (p₂ : a₂ == a₃) (p₃ : a₃ == a₄) (p₄ : a₄ == a₅)
      → (p₀ ∙ ((p₁ ∙ p₂) ∙' p₃)) ∙' p₄ == ((p₀ ∙ p₁) ∙ p₂) ∙' (p₃ ∙ p₄)
    ap-mega-assoc idp p₁ p₂ idp p₄ = idp
    abstract
      lemma : ∀ c → idp == idp
        [ (λ p → Pushout-fmap (SpanMap-∘ span-map₁₂ span-map₀₁) p
              == Pushout-fmap span-map₁₂ (Pushout-fmap span-map₀₁ p))
          ↓ glue c ]
      lemma c = ↓-='-in' $
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
          =∎

∘-Pushout-fmap : ∀ {i₀ j₀ k₀ i₁ j₁ k₁ i₂ j₂ k₂} {span₀ : Span {i₀} {j₀} {k₀}}
  {span₁ : Span {i₁} {j₁} {k₁}} {span₂ : Span {i₂} {j₂} {k₂}}
  (span-map₁₂ : SpanMap span₁ span₂) (span-map₀₁ : SpanMap span₀ span₁)
  → ∀ p → Pushout-fmap span-map₁₂ (Pushout-fmap span-map₀₁ p)
       == Pushout-fmap (SpanMap-∘ span-map₁₂ span-map₀₁) p
∘-Pushout-fmap span-map₁₂ span-map₀₁ p = ! (Pushout-fmap-∘ span-map₁₂ span-map₀₁ p)

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
    hA-ise = fst span-ise
    hB-ise = fst (snd span-ise)
    hC-ise = snd (snd span-ise)
    module hA-ise = is-equiv hA-ise
    module hB-ise = is-equiv hB-ise
    module hC-ise = is-equiv hC-ise

    to = To.f
    from = From.f

    abstract
      to-from' : ∀ y → Pushout-fmap (SpanMap-∘ span-to span-from) y == y
      to-from' = Pushout-elim (ap left ∘ hA-ise.f-g) (ap right ∘ hB-ise.f-g)
        (λ c → ↓-app=idf-from-square $
                PushoutFmap.glue-β (SpanMap-∘ span-to span-from) c
            ∙v⊡ ap2 _∙'_
                  (CommSquare-inverse-inv-r span-to.f-commutes hC-ise hA-ise c
                    |in-ctx ap left |in-ctx _∙ glue (span-to.hC (span-from.hC c)))
                  (CommSquare-inverse-inv-r span-to.g-commutes hC-ise hB-ise c
                    |in-ctx ! |in-ctx ap right)
            ∙v⊡ ap2 _∙'_
                  ( ap-∙ left (hA-ise.f-g (span₁.f c)) (! (ap span₁.f (hC-ise.f-g c)))
                    |in-ctx _∙ glue (span-to.hC (span-from.hC c)))
                  ( !-∙ (hB-ise.f-g (span₁.g c)) (! (ap span₁.g (hC-ise.f-g c)))
                    |in-ctx ap right)
            ∙v⊡ ap2 _∙'_
                  ( ap-! left (ap span₁.f (hC-ise.f-g c))
                    |in-ctx ap left (hA-ise.f-g (span₁.f c)) ∙_
                    |in-ctx _∙ glue (span-to.hC (span-from.hC c)))
                  ( ap-∙ right
                    (! (! (ap span₁.g (hC-ise.f-g c))))
                    (! (hB-ise.f-g (span₁.g c))))
            ∙v⊡ ( ap2 _∙_
                    ( !-! (ap span₁.g (hC-ise.f-g c))
                      |in-ctx ap right)
                    ( ap-! right (hB-ise.f-g (span₁.g c)))
                  |in-ctx ( ( ap left (hA-ise.f-g (span₁.f c))
                              ∙ ! (ap left (ap span₁.f (hC-ise.f-g c))))
                            ∙ glue (span-to.hC (span-from.hC c)))
                          ∙'_)
            ∙v⊡ ap2 _∙'_
                  ( ∘-ap left span₁.f (hC-ise.f-g c)
                    |in-ctx !
                    |in-ctx ap left (hA-ise.f-g (span₁.f c)) ∙_
                    |in-ctx _∙ glue (span-to.hC (span-from.hC c)))
                  ( ∘-ap right span₁.g (hC-ise.f-g c)
                    |in-ctx _∙ ! (ap right (hB-ise.f-g (span₁.g c))))
            ∙v⊡ ( ( lt-square (ap left (hA-ise.f-g (span₁.f c)))
                    ⊡h rt-square (ap (left ∘ span₁.f) (hC-ise.f-g c)))
                  ⊡h square-symmetry (natural-square glue (hC-ise.f-g c)))
            ⊡h' lt-square (ap (right ∘ span₁.g) (hC-ise.f-g c))
            ⊡h rt-square (ap right (hB-ise.f-g (span₁.g c))))

    to-from : ∀ y → to (from y) == y
    to-from y = ∘-Pushout-fmap span-to span-from y ∙ to-from' y

    abstract
      from-to' : ∀ x → Pushout-fmap (SpanMap-∘ span-from span-to) x == x
      from-to' = Pushout-elim (ap left ∘ hA-ise.g-f) (ap right ∘ hB-ise.g-f)
        (λ c → ↓-app=idf-from-square $
                PushoutFmap.glue-β (SpanMap-∘ span-from span-to) c
            ∙v⊡ ap2 _∙'_
                  (CommSquare-inverse-inv-l span-to.f-commutes hC-ise hA-ise c
                    |in-ctx ap left |in-ctx _∙ glue (span-from.hC (span-to.hC c)))
                  (CommSquare-inverse-inv-l span-to.g-commutes hC-ise hB-ise c
                    |in-ctx ! |in-ctx ap right)
            ∙v⊡ ap2 _∙'_
                  ( ap-∙ left (hA-ise.g-f (span₀.f c)) (! (ap span₀.f (hC-ise.g-f c)))
                    |in-ctx _∙ glue (span-from.hC (span-to.hC c)))
                  ( !-∙ (hB-ise.g-f (span₀.g c)) (! (ap span₀.g (hC-ise.g-f c)))
                    |in-ctx ap right)
            ∙v⊡ ap2 _∙'_
                  ( ap-! left (ap span₀.f (hC-ise.g-f c))
                    |in-ctx ap left (hA-ise.g-f (span₀.f c)) ∙_
                    |in-ctx _∙ glue (span-from.hC (span-to.hC c)))
                  ( ap-∙ right
                    (! (! (ap span₀.g (hC-ise.g-f c))))
                    (! (hB-ise.g-f (span₀.g c))))
            ∙v⊡ ( ap2 _∙_
                    ( !-! (ap span₀.g (hC-ise.g-f c))
                      |in-ctx ap right)
                    ( ap-! right (hB-ise.g-f (span₀.g c)))
                  |in-ctx ( ( ap left (hA-ise.g-f (span₀.f c))
                              ∙ ! (ap left (ap span₀.f (hC-ise.g-f c))))
                            ∙ glue (span-from.hC (span-to.hC c)))
                          ∙'_)
            ∙v⊡ ap2 _∙'_
                  ( ∘-ap left span₀.f (hC-ise.g-f c)
                    |in-ctx !
                    |in-ctx ap left (hA-ise.g-f (span₀.f c)) ∙_
                    |in-ctx _∙ glue (span-from.hC (span-to.hC c)))
                  ( ∘-ap right span₀.g (hC-ise.g-f c)
                    |in-ctx _∙ ! (ap right (hB-ise.g-f (span₀.g c))))
            ∙v⊡ ( ( lt-square (ap left (hA-ise.g-f (span₀.f c)))
                    ⊡h rt-square (ap (left ∘ span₀.f) (hC-ise.g-f c)))
                  ⊡h square-symmetry (natural-square glue (hC-ise.g-f c)))
            ⊡h' lt-square (ap (right ∘ span₀.g) (hC-ise.g-f c))
            ⊡h rt-square (ap right (hB-ise.g-f (span₀.g c))))

    from-to : ∀ x → from (to x) == x
    from-to x = ∘-Pushout-fmap span-from span-to x ∙ from-to' x

  Pushout-emap : Pushout span₀ ≃ Pushout span₁
  Pushout-emap = equiv to from to-from from-to
