{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.TwoPushouts where

--        g     h
--     D --> B --> C    K = A ⊔^D B / (f,g)       d₁ = A <- D -> B
--    f|     |     |    L = K ⊔^B C / (right,h)   d₂ = K <- B -> C
--     v     v     v                              d  = A <- D -> D
--     A --> K --> L
--
module TwoPushoutsRSplit {i j k l} {A : Type i} {B : Type j} {C : Type k}
  {D : Type l} (f : D → A) (g : D → B) (h : B → C) where

  private
    d₁ : Span
    d₁ = span A B D f g

    d₂ : Span
    d₂ = span (Pushout d₁) C B right h

    d : Span
    d = span A C D f (h ∘ g)

  module Inner = PushoutRec {d = d₁} {D = Pushout d}
    left
    (right ∘ h)
    glue

  module Split = PushoutRec {d = d} {D = Pushout d₂}
    (left ∘ left)
    right
    (λ b → ap left (glue b) ∙ glue (g b))

  split : Pushout d -> Pushout d₂
  split = Split.f

  module Merge = PushoutRec {d = d₂} {D = Pushout d}
    Inner.f
    right
    (λ _ → idp)

  merge : Pushout d₂ → Pushout d
  merge = Merge.f

  private
    square-extend-tr : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ b : A}
      {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀}
      {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁} (q : a₁₀ == b)
      → Square p₀₋ p₋₀ p₋₁ p₁₋
      → Square p₀₋ (p₋₀ ∙ q) p₋₁ (! q ∙' p₁₋)
    square-extend-tr idp ids = ids

    square-corner-bl : ∀ {i} {A : Type i} {a₀ a₁ : A} (q : a₀ == a₁)
      → Square (! q) idp q idp
    square-corner-bl idp = ids

  split-inner : (k : Pushout d₁) → split (Inner.f k) == left k
  split-inner = Pushout-elim
    (λ a → idp)
    (λ c → ! (glue c))
    (λ b → ↓-='-from-square $
      (ap-∘ split Inner.f (glue b)
       ∙ ap (ap split) (Inner.glue-β b) ∙ Split.glue-β b)
      ∙v⊡ square-extend-tr (glue (g b)) vid-square)

  abstract
    split-merge : (l : Pushout d₂) → split (merge l) == l
    split-merge = Pushout-elim
      split-inner
      (λ d → idp)
      (λ c → ↓-∘=idf-from-square split merge $
        ap (ap split) (Merge.glue-β c) ∙v⊡ square-corner-bl (glue c))


    merge-split : (l : Pushout d) → merge (split l) == l
    merge-split = Pushout-elim
      (λ a → idp)
      (λ d → idp)
      (λ b → ↓-∘=idf-from-square merge split $ vert-degen-square $
        ap merge (ap split (glue b))
          =⟨ ap (ap merge) (Split.glue-β b) ⟩
        ap merge (ap left (glue b) ∙ glue (g b))
          =⟨ ap-∙ merge (ap left (glue b)) (glue (g b)) ⟩
        ap merge (ap left (glue b)) ∙ ap merge (glue (g b))
          =⟨ ∘-ap merge left (glue b) |in-ctx (λ w → w ∙ ap merge (glue (g b))) ⟩
        ap Inner.f (glue b) ∙ ap merge (glue (g b))
          =⟨ Merge.glue-β (g b) |in-ctx (λ w → ap Inner.f (glue b) ∙ w) ⟩
        ap Inner.f (glue b) ∙ idp
          =⟨ ∙-unit-r _ ⟩
        ap Inner.f (glue b)
          =⟨ Inner.glue-β b ⟩
        glue b ∎)


  split-equiv : Pushout d ≃ Pushout d₂
  split-equiv = equiv split merge split-merge merge-split

{-
  two-pushouts : Lift {j = lmax l (lmax k (lmax j i))} (Pushout d) == Pushout d₂
  two-pushouts = ua (two-pushouts-equiv ∘e lift-equiv)

  two-pushouts-left : lift ∘ left == left ∘ left
                      [ (λ E → (A → E)) ↓ two-pushouts ]
  two-pushouts-left = codomain-over-equiv _ _

  two-pushouts-right : lift ∘ right == right [ (λ E → (D → E)) ↓ two-pushouts ]
  two-pushouts-right = codomain-over-equiv _ _

  two-pushouts-inner : lift ∘ Inner.f == left
                       [ (λ E → (Pushout d₁ → E)) ↓ two-pushouts ]
  two-pushouts-inner = codomain-over-equiv _ _ ▹ λ= split-inner
-}

rsplit-pushouts-equiv = TwoPushoutsRSplit.split-equiv

--        h
--     D --> C    K = A ⊔^D C / (f,h)       d₁ = A <- D -> C
--    f|     |    L = B ⊔^A K / (g,left)    d₂ = B <- A -> K
--     v     v                              d  = B <- D -> C
--     A --> K
--    g|     |
--     v     v
--     B --> L

module TwoPushoutsLSplit {i j k l} {A : Type i} {B : Type j} {C : Type k}
  {D : Type l} (f : D → A) (g : A → B) (h : D → C) where
  private
    d₁ : Span
    d₁ = span A C D f h

    d₂ : Span
    d₂ = span B (Pushout d₁) A g left

    d : Span
    d = span B C D (g ∘ f) h

  split-equiv : Pushout d ≃ Pushout d₂
  split-equiv =
    Pushout d
      ≃⟨ Pushout-flip-equiv d ⟩
    Pushout (Span-flip d)
      ≃⟨ rsplit-pushouts-equiv h f g ⟩
    Pushout (span (Pushout (Span-flip d₁)) B A right g)
      ≃⟨ Pushout-flip-equiv (span (Pushout (Span-flip d₁)) B A right g) ⟩
    Pushout (span B (Pushout (Span-flip d₁)) A g right)
      ≃⟨ Pushout-emap
          ( span-map (idf B) Pushout-flip (idf A) (comm-sqr λ _ → idp) (comm-sqr λ _ → idp)
          , idf-is-equiv _ , snd (Pushout-flip-equiv (Span-flip d₁)) , idf-is-equiv _) ⟩
    Pushout d₂
      ≃∎

lsplit-pushouts-equiv = TwoPushoutsLSplit.split-equiv


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

  two-pushouts-⊙inner : ⊙lift ⊙∘ (Inner.f , idp) == ⊙left ps₂
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
