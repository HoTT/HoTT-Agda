{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.PushoutSplit where

--        g     h
--     D --> B --> C    K = A ⊔^D B / (f,g)       d₁ = A <- D -> B
--    f|     |     |    L = K ⊔^B C / (right,h)   d₂ = K <- B -> C
--     v     v     v                              d  = A <- D -> C
--     A --> K --> L
--
module PushoutRSplit {i j k l} {A : Type i} {B : Type j} {C : Type k}
  {D : Type l} (f : D → A) (g : D → B) (h : B → C) where

  private
    d₁ : Span
    d₁ = span A B D f g

    d₂ : Span
    d₂ = span (Pushout d₁) C B right h

    d : Span
    d = span A C D f (h ∘ g)

  split-span-map : SpanMap d d₂
  split-span-map = span-map left (idf C) g (comm-sqr λ a → glue a) (comm-sqr λ _ → idp)

  module Split = PushoutFmap split-span-map

  split : Pushout d → Pushout d₂
  split = Split.f

  inner-span-map : SpanMap d₁ d
  inner-span-map = span-map (idf A) h (idf D) (comm-sqr λ _ → idp) (comm-sqr λ _ → idp)

  module Inner = PushoutFmap inner-span-map

  inner : Pushout d₁ → Pushout d
  inner = Inner.f

  module Merge = PushoutRec {d = d₂} {D = Pushout d}
    inner right (λ _ → idp)

  merge : Pushout d₂ → Pushout d
  merge = Merge.f

  private
    square-extend-tr : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ b : A}
      {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
      {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁} (q : a₁₀ == b)
      → Square p₀₋ p₋₀ p₋₁ p₁₋
      → Square p₀₋ (p₋₀ ∙ q) p₋₁ (! q ∙' p₁₋)
    square-extend-tr idp ids = ids

  split-inner : (k : Pushout d₁) → split (inner k) == left k
  split-inner = Pushout-elim
    (λ a → idp)
    (λ b → ! (glue b))
    (λ d → ↓-='-from-square $
      (ap-∘ split inner (glue d)
       ∙ ap (ap split) (Inner.glue-β d) ∙ Split.glue-β d)
      ∙v⊡ square-extend-tr (glue (g d)) vid-square)

  abstract
    split-merge : (l : Pushout d₂) → split (merge l) == l
    split-merge = Pushout-elim
      split-inner
      (λ c → idp)
      (λ b → ↓-∘=idf-from-square split merge $
        ap (ap split) (Merge.glue-β b) ∙v⊡ bl-square (glue b))


    merge-split : (l : Pushout d) → merge (split l) == l
    merge-split = Pushout-elim
      (λ a → idp)
      (λ c → idp)
      (λ d → ↓-∘=idf-in' merge split $
        ap merge (ap split (glue d))
          =⟨ ap (ap merge) (Split.glue-β d) ⟩
        ap merge (ap left (glue d) ∙ glue (g d))
          =⟨ ap-∙ merge (ap left (glue d)) (glue (g d)) ⟩
        ap merge (ap left (glue d)) ∙ ap merge (glue (g d))
          =⟨ ap2 _∙_ (∘-ap merge left (glue d)) (Merge.glue-β (g d)) ⟩
        ap inner (glue d) ∙ idp
          =⟨ ∙-unit-r _ ⟩
        ap inner (glue d)
          =⟨ Inner.glue-β d ⟩
        glue d ∎)


  split-equiv : Pushout d ≃ Pushout d₂
  split-equiv = equiv split merge split-merge merge-split

{-
  two-pushouts-left : lift ∘ left == left ∘ left
                      [ (λ E → (A → E)) ↓ two-pushouts ]
  two-pushouts-left = codomain-over-equiv _ _

  two-pushouts-right : lift ∘ right == right [ (λ E → (D → E)) ↓ two-pushouts ]
  two-pushouts-right = codomain-over-equiv _ _

  two-pushouts-inner : lift ∘ inner == left
                       [ (λ E → (Pushout d₁ → E)) ↓ two-pushouts ]
  two-pushouts-inner = codomain-over-equiv _ _ ▹ λ= split-inner
-}

rsplit-equiv = PushoutRSplit.split-equiv

--        h
--     D --> C    K = A ⊔^D C / (f,h)       d₁ = A <- D -> C
--    f|     |    L = B ⊔^A K / (g,left)    d₂ = B <- A -> K
--     v     v                              d  = B <- D -> C
--     A --> K
--    g|     |
--     v     v
--     B --> L

module PushoutLSplit {i j k l} {A : Type i} {B : Type j} {C : Type k}
  {D : Type l} (f : D → A) (g : A → B) (h : D → C) where

  private
    d₁ : Span
    d₁ = span A C D f h

    d₂ : Span
    d₂ = span B (Pushout d₁) A g left

    d : Span
    d = span B C D (g ∘ f) h

  split-span-map : SpanMap d d₂
  split-span-map = span-map (idf B) right f (comm-sqr λ _ → idp) (comm-sqr λ d → ! (glue d))

  module Split = PushoutFmap split-span-map

  split : Pushout d → Pushout d₂
  split = Split.f

  inner-span-map : SpanMap d₁ d
  inner-span-map = span-map g (idf C) (idf D) (comm-sqr λ _ → idp) (comm-sqr λ _ → idp)

  module Inner = PushoutFmap inner-span-map

  inner : Pushout d₁ → Pushout d
  inner = Inner.f

  module Merge = PushoutRec {d = d₂} {D = Pushout d}
    left inner (λ _ → idp)

  merge : Pushout d₂ → Pushout d
  merge = Merge.f

  private
    square-extend-tl : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ b : A}
      {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
      {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁} (q : b == a₀₀)
      → Square p₀₋ p₋₀ p₋₁ p₁₋
      → Square (q ∙' p₀₋) (q ∙' p₋₀) p₋₁ p₁₋
    square-extend-tl idp ids = ids

  split-inner : (k : Pushout d₁) → split (inner k) == right k
  split-inner = Pushout-elim
    (λ a → glue a)
    (λ c → idp)
    (λ d → ↓-='-from-square $
      (ap-∘ split inner (glue d)
       ∙ ap (ap split) (Inner.glue-β d) ∙ Split.glue-β d
       ∙ ap (λ p → glue (f d) ∙' ap right p) (!-! (glue d)))
      ∙v⊡ square-extend-tl (glue (f d)) vid-square)

  abstract
    split-merge : (l : Pushout d₂) → split (merge l) == l
    split-merge = Pushout-elim
      (λ b → idp)
      split-inner
      (λ a → ↓-∘=idf-from-square split merge $
        ap (ap split) (Merge.glue-β a) ∙v⊡ br-square (glue a))


    merge-split : (l : Pushout d) → merge (split l) == l
    merge-split = Pushout-elim
      (λ b → idp)
      (λ c → idp)
      (λ d → ↓-∘=idf-in' merge split $
        ap merge (ap split (glue d))
          =⟨ ap (ap merge) (Split.glue-β d) ⟩
        ap merge (glue (f d) ∙' ap right (! (! (glue d))))
          =⟨ ap-∙' merge (glue (f d)) (ap right (! (! (glue d)))) ⟩
        ap merge (glue (f d)) ∙' ap merge (ap right (! (! (glue d))))
          =⟨ ap2 _∙'_ (Merge.glue-β (f d)) (∘-ap merge right (! (! (glue d)))) ⟩
        idp ∙' ap inner (! (! (glue d)))
          =⟨ ∙'-unit-l _ ⟩
        ap inner (! (! (glue d)))
          =⟨ ap (ap inner) (!-! (glue d)) ⟩
        ap inner (glue d)
          =⟨ Inner.glue-β d ⟩
        glue d ∎)


  split-equiv : Pushout d ≃ Pushout d₂
  split-equiv = equiv split merge split-merge merge-split

lsplit-equiv = PushoutLSplit.split-equiv


{- TODO Update this part

--        g     h
--     Y --> Z --> W    K = X ⊔^Y Y / (f,g)        ps₁ = X <- Y -> Z
--    f|     |     |    L = Z ⊔^Z W / (left,h)     ps₂ = K <- Z -> W
--     v     v     v                               ps = X <- Y -> W
--     X --> K --> L
--
module TwoPushoutsPtd {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (f : Y ⊙→ X) (g : Y ⊙→ Z) (h : Z ⊙→ W) where

  private
    ps₁ = ⊙span X Z Y f g
    ps₂ = ⊙span (⊙Pushout ps₁) W Z (⊙right ps₁) h
    ps = ⊙span X W Y f (h ⊙∘ g)

  open TwoPushoutsEquiv (fst f) (fst g) (fst h)

  two-pushouts-ptd :
    ⊙Lift {j = lmax l (lmax k (lmax j i))} (⊙Pushout ps)
    == ⊙Pushout ps₂
  two-pushouts-ptd = ⊙ua (two-pushouts-equiv ∘e lift-equiv) idp

  two-pushouts-⊙left :
    ⊙lift ⊙∘ ⊙left ps == ⊙left ps₂ ⊙∘ ⊙left ps₁
    [ (λ V → X ⊙→ V) ↓ two-pushouts-ptd ]
  two-pushouts-⊙left = codomain-over-⊙equiv _ _ _

  two-pushouts-⊙right :
    ⊙lift ⊙∘ ⊙right ps == ⊙right ps₂
    [ (λ V → W ⊙→ V) ↓ two-pushouts-ptd ]
  two-pushouts-⊙right =
    codomain-over-⊙equiv _ _ _ ▹ pair= idp (lemma f g h)
    where
    lemma : {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
      (f : Y ⊙→ X) (g : Y ⊙→ Z) (h : Z ⊙→ W)
      → ap (TwoPushoutsEquiv.split (fst f) (fst g) (fst h)
               ∘ lower {j = lmax l (lmax k (lmax j i))})
              (snd (⊙lift ⊙∘ ⊙right (⊙span X W Y f (h ⊙∘ g))))
        ∙ idp
        ==  ap right (! (snd h)) ∙ ! (glue (snd Z))
            ∙' ap left (snd (⊙right (⊙span X Z Y f g)))
    lemma {Y = Y} (f , idp) (g , idp) (h , idp) =
      ap (2P.split ∘ lower) (ap lift (! (glue (snd Y))) ∙ idp) ∙ idp
        =⟨ ∙-unit-r _ ⟩
      ap (2P.split ∘ lower) (ap lift (! (glue (snd Y))) ∙ idp)
        =⟨ ∙-unit-r _ |in-ctx (ap (2P.split ∘ lower)) ⟩
      ap (2P.split ∘ lower) (ap lift (! (glue (snd Y))))
        =⟨ ∘-ap (2P.split ∘ lower) lift _ ⟩
      ap 2P.split (! (glue (snd Y)))
        =⟨ ap-! 2P.split (glue (snd Y)) ⟩
      ! (ap 2P.split (glue (snd Y)))
        =⟨ 2P.Split.glue-β (snd Y) |in-ctx ! ⟩
      ! (ap left (glue (snd Y)) ∙ glue (g (snd Y)))
        =⟨ !-∙ (ap left (glue (snd Y))) (glue (g (snd Y))) ⟩
      ! (glue (g (snd Y))) ∙ ! (ap left (glue (snd Y)))
        =⟨ !-ap left (glue (snd Y)) |in-ctx (λ w → ! (glue (g (snd Y))) ∙ w) ⟩
      ! (glue (g (snd Y))) ∙ ap left (! (glue (snd Y)))
        =⟨ ∙=∙' (! (glue (g (snd Y)))) (ap left (! (glue (snd Y)))) ⟩
      ! (glue (g (snd Y))) ∙' ap left (! (glue (snd Y))) ∎
      where
      module 2P = TwoPushoutsEquiv f g h

  two-pushouts-⊙inner : ⊙lift ⊙∘ (inner , idp) == ⊙left ps₂
    [ (λ V → ⊙Pushout ps₁ ⊙→ V) ↓ two-pushouts-ptd ]
  two-pushouts-⊙inner =
    codomain-over-⊙equiv _ _ _ ▹ ⊙λ= split-inner idp
-}

{-
open TwoPushoutsEquiv using () renaming (split-equiv to vsplit-pushouts-equiv)
  -- two-pushouts; two-pushouts-left; two-pushouts-right; two-pushouts-inner

open TwoPushoutsPtd
  using (two-pushouts-ptd; two-pushouts-⊙left; two-pushouts-⊙right;
         two-pushouts-⊙inner)
-}
