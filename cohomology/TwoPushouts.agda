{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.FunctionOver

module cohomology.TwoPushouts where

--        g     h
--     B --> C --> D    K = A ⊔^B C / (f,g)        d₁ = A <- B -> C
--    f|     |     |    L = K ⊔^C D / (left,h)     d₂ = K <- C -> D
--     v     v     v                               d  = A <- B -> D
--     A --> K --> L
--
module TwoPushoutsEquiv {i j k l} {A : Type i} {B : Type j} {C : Type k}
  {D : Type l} (f : B → A) (g : B → C) (h : C → D) where

  private
    d₁ : Span
    d₁ = span A C B f g


    d₂ : Span
    d₂ = span (Pushout d₁) D C right h

    d : Span
    d = span A D B f (h ∘ g)

  module Inner = PushoutRec {d = d₁} {D = Pushout d}
    left
    (right ∘ h)
    glue

  module Into = PushoutRec {d = d} {D = Pushout d₂}
    (left ∘ left)
    right
    (λ b → ap left (glue b) ∙ glue (g b))

  into : Pushout d -> Pushout d₂
  into = Into.f

  module Out = PushoutRec {d = d₂} {D = Pushout d}
    Inner.f
    right
    (λ _ → idp)

  out : Pushout d₂ → Pushout d
  out = Out.f

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

  into-inner : (k : Pushout d₁) → into (Inner.f k) == left k
  into-inner = Pushout-elim
    (λ a → idp)
    (λ c → ! (glue c))
    (λ b → ↓-='-from-square $
      (ap-∘ into Inner.f (glue b)
       ∙ ap (ap into) (Inner.glue-β b) ∙ Into.glue-β b)
      ∙v⊡ square-extend-tr (glue (g b)) vid-square)

  abstract
    into-out : (l : Pushout d₂) → into (out l) == l
    into-out = Pushout-elim
      into-inner
      (λ d → idp)
      (λ c → ↓-∘=idf-from-square into out $
        ap (ap into) (Out.glue-β c) ∙v⊡ square-corner-bl (glue c))


    out-into : (l : Pushout d) → out (into l) == l
    out-into = Pushout-elim
      (λ a → idp)
      (λ d → idp)
      (λ b → ↓-∘=idf-from-square out into $ vert-degen-square $
        ap out (ap into (glue b))
          =⟨ ap (ap out) (Into.glue-β b) ⟩
        ap out (ap left (glue b) ∙ glue (g b))
          =⟨ ap-∙ out (ap left (glue b)) (glue (g b)) ⟩
        ap out (ap left (glue b)) ∙ ap out (glue (g b))
          =⟨ ∘-ap out left (glue b) |in-ctx (λ w → w ∙ ap out (glue (g b))) ⟩
        ap Inner.f (glue b) ∙ ap out (glue (g b))
          =⟨ Out.glue-β (g b) |in-ctx (λ w → ap Inner.f (glue b) ∙ w) ⟩
        ap Inner.f (glue b) ∙ idp
          =⟨ ∙-unit-r _ ⟩
        ap Inner.f (glue b)
          =⟨ Inner.glue-β b ⟩
        glue b ∎)


  two-pushouts-equiv : Pushout d ≃ Pushout d₂
  two-pushouts-equiv = equiv into out into-out out-into

  two-pushouts : Lift {j = lmax l (lmax k (lmax j i))} (Pushout d) == Pushout d₂
  two-pushouts = ua (two-pushouts-equiv ∘e lift-equiv)

  two-pushouts-left : lift ∘ left == left ∘ left
                      [ (λ E → (A → E)) ↓ two-pushouts ]
  two-pushouts-left = codomain-over-equiv _ _

  two-pushouts-right : lift ∘ right == right [ (λ E → (D → E)) ↓ two-pushouts ]
  two-pushouts-right = codomain-over-equiv _ _

  two-pushouts-inner : lift ∘ Inner.f == left
                       [ (λ E → (Pushout d₁ → E)) ↓ two-pushouts ]
  two-pushouts-inner = codomain-over-equiv _ _ ▹ λ= into-inner


--        g     h
--     Y --> Z --> W    K = X ⊔^Y Y / (f,g)        ps₁ = X <- Y -> Z
--    f|     |     |    L = Z ⊔^Z W / (left,h)     ps₂ = K <- Z -> W
--     v     v     v                               ps = X <- Y -> W
--     X --> K --> L
--
module TwoPushoutsPtd {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (f : fst (Y ∙→ X)) (g : fst (Y ∙→ Z)) (h : fst (Z ∙→ W)) where

  private
    ps₁ = ptd-span X Z Y f g
    ps₂ = ptd-span (Ptd-Pushout ps₁) W Z (ptd-right {d = ps₁}) h
    ps = ptd-span X W Y f (h ∘ptd g)

  open TwoPushoutsEquiv (fst f) (fst g) (fst h) public

  two-pushouts-ptd :
    Ptd-Lift {j = lmax l (lmax k (lmax j i))} (Ptd-Pushout ps)
    == Ptd-Pushout ps₂
  two-pushouts-ptd = ptd-ua (two-pushouts-equiv ∘e lift-equiv) idp

  two-pushouts-ptd-left :
    ptd-lift ∘ptd ptd-left {d = ps}
    == ptd-left {d = ps₂} ∘ptd ptd-left {d = ps₁}
    [ (λ V → fst (X ∙→ V)) ↓ two-pushouts-ptd ]
  two-pushouts-ptd-left = codomain-over-ptd-equiv _ _ _

  two-pushouts-ptd-right :
    ptd-lift ∘ptd ptd-right {d = ps} == ptd-right {d = ps₂}
    [ (λ V → fst (W ∙→ V)) ↓ two-pushouts-ptd ]
  two-pushouts-ptd-right =
    codomain-over-ptd-equiv _ _ _ ▹ pair= idp (lemma f g h)
    where
    lemma : {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
      (f : fst (Y ∙→ X)) (g : fst (Y ∙→ Z)) (h : fst (Z ∙→ W))
      → ap (TwoPushoutsEquiv.into (fst f) (fst g) (fst h)
               ∘ lower {j = lmax l (lmax k (lmax j i))})
              (snd (ptd-lift ∘ptd ptd-right {d = ptd-span X W Y f (h ∘ptd g)}))
        ∙ idp
        ==  ap right (! (snd h)) ∙ ! (glue (snd Z))
            ∙' ap left (snd (ptd-right {d = ptd-span X Z Y f g}))
    lemma {Y = Y} (f , idp) (g , idp) (h , idp) =
      ap (2P.into ∘ lower) (ap lift (! (glue (snd Y))) ∙ idp) ∙ idp
        =⟨ ∙-unit-r _ ⟩
      ap (2P.into ∘ lower) (ap lift (! (glue (snd Y))) ∙ idp)
        =⟨ ∙-unit-r _ |in-ctx (ap (2P.into ∘ lower)) ⟩
      ap (2P.into ∘ lower) (ap lift (! (glue (snd Y))))
        =⟨ ∘-ap (2P.into ∘ lower) lift _ ⟩
      ap 2P.into (! (glue (snd Y)))
        =⟨ ap-! 2P.into (glue (snd Y)) ⟩
      ! (ap 2P.into (glue (snd Y)))
        =⟨ 2P.Into.glue-β (snd Y) |in-ctx ! ⟩
      ! (ap left (glue (snd Y)) ∙ glue (g (snd Y)))
        =⟨ !-∙ (ap left (glue (snd Y))) (glue (g (snd Y))) ⟩
      ! (glue (g (snd Y))) ∙ ! (ap left (glue (snd Y)))
        =⟨ !-ap left (glue (snd Y)) |in-ctx (λ w → ! (glue (g (snd Y))) ∙ w) ⟩
      ! (glue (g (snd Y))) ∙ ap left (! (glue (snd Y)))
        =⟨ ∙=∙' (! (glue (g (snd Y)))) (ap left (! (glue (snd Y)))) ⟩
      ! (glue (g (snd Y))) ∙' ap left (! (glue (snd Y))) ∎
      where
      module 2P = TwoPushoutsEquiv f g h

  ptd-into-inner :
    ((TwoPushoutsEquiv.into (fst f) (fst g) (fst h) ∘ Inner.f) , idp)
    == ptd-left {d = ps₂}
  ptd-into-inner = pair= (λ= into-inner) $ ↓-app=cst-in $
    ! (∙-unit-r _ ∙ app=-β into-inner (left (snd X)))

  two-pushouts-ptd-inner : ptd-lift ∘ptd (Inner.f , idp) == ptd-left {d = ps₂}
    [ (λ V → fst (Ptd-Pushout ps₁ ∙→ V)) ↓ two-pushouts-ptd ]
  two-pushouts-ptd-inner =
    codomain-over-ptd-equiv _ _ _ ▹ ptd-into-inner

open TwoPushoutsEquiv
  using (two-pushouts-equiv; two-pushouts; two-pushouts-left;
         two-pushouts-right; two-pushouts-inner)

open TwoPushoutsPtd
  using (two-pushouts-ptd; two-pushouts-ptd-left; two-pushouts-ptd-right;
         two-pushouts-ptd-inner)
