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

  module KToL = PushoutRec {d = d₁} {D = Pushout d}
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
    KToL.f
    right
    (λ _ → idp)

  out : Pushout d₂ → Pushout d
  out = Out.f

  abstract
    into-out : (l : Pushout d₂) → into (out l) == l
    into-out = Pushout-elim
      (Pushout-elim
        (λ a → idp)
        (λ c → ! (glue c))
        (λ b → ↓-='-in
          (ap left (glue b)
             =⟨ ! (∙-unit-r _) ⟩
           ap left (glue b) ∙ idp
             =⟨ ! (!-inv-r (glue (g b)))
               |in-ctx (λ w → ap left (glue b) ∙ w) ⟩
           ap left (glue b) ∙ (glue (g b) ∙ ! (glue (g b)))
             =⟨ ! (∙-assoc (ap left (glue b)) (glue (g b)) _) ⟩
           (ap left (glue b) ∙ glue (g b)) ∙ ! (glue (g b))
             =⟨ ∙=∙' (ap left (glue b) ∙ glue (g b)) (! (glue (g b))) ⟩
           (ap left (glue b) ∙ glue (g b)) ∙' ! (glue (g b))
             =⟨ ! (Into.glue-β b) |in-ctx (λ w → w ∙' ! (glue (g b))) ⟩
           ap into (glue b) ∙' ! (glue (g b))
             =⟨ ! (KToL.glue-β b) |in-ctx (λ w → ap into w ∙' ! (glue (g b))) ⟩
           ap into (ap (out ∘ left) (glue b)) ∙' ! (glue (g b))
             =⟨ ∘-ap into (out ∘ left) (glue b)
               |in-ctx (λ w → w ∙' ! (glue (g b))) ⟩
           ap (into ∘ out ∘ left) (glue b) ∙' ! (glue (g b)) ∎)))
      (λ d → idp)
      (λ c → ↓-app=idf-in
        (! (glue c) ∙' glue c
           =⟨ ∙'=∙ (! (glue c)) (glue c) ⟩
         ! (glue c) ∙ glue c
           =⟨ !-inv-l (glue c) ⟩
         idp
           =⟨ ! (Out.glue-β c) |in-ctx (λ w → ap into w) ⟩
         ap into (ap out (glue c))
           =⟨ ∘-ap into out (glue c) ⟩
         ap (into ∘ out) (glue c)
           =⟨ ! (∙-unit-r _) ⟩
         ap (into ∘ out) (glue c) ∙ idp ∎ ))

    out-into : (l : Pushout d) → out (into l) == l
    out-into = Pushout-elim
      (λ a → idp)
      (λ d → idp)
      (λ b → ↓-app=idf-in
        (idp ∙' glue b
           =⟨ ∙'-unit-l _ ⟩
         glue b
           =⟨ ! (∙-unit-r _) ⟩
         glue b ∙ idp
           =⟨ ! (Out.glue-β (g b)) |in-ctx (λ w → glue b ∙ w) ⟩
         glue b ∙ ap out (glue (g b))
           =⟨ ! (KToL.glue-β b)
             |in-ctx (λ w → w ∙ ap out (glue (g b))) ⟩
         ap (out ∘ left) (glue b) ∙ ap out (glue (g b))
           =⟨ ap-∘ out left (glue b)
             |in-ctx (λ w → w ∙ ap out (glue (g b))) ⟩
         ap out (ap left (glue b)) ∙ ap out (glue (g b))
           =⟨ ∙-ap out (ap left (glue b)) (glue (g b)) ⟩
         ap out (ap left (glue b) ∙ glue (g b))
           =⟨ ! (Into.glue-β b) |in-ctx (λ w → ap out w) ⟩
         ap out (ap into (glue b))
           =⟨ ∘-ap out into (glue b) ⟩
         ap (out ∘ into) (glue b)
           =⟨ ! (∙-unit-r _) ⟩
         ap (out ∘ into) (glue b) ∙ idp ∎))


  two-pushouts-equiv : Pushout d ≃ Pushout d₂
  two-pushouts-equiv = equiv into out into-out out-into

  two-pushouts : Lift {j = lmax l (lmax k (lmax j i))} (Pushout d) == Pushout d₂
  two-pushouts = ua (two-pushouts-equiv ∘e lift-equiv)

  two-pushouts-left : lift ∘ left == left ∘ left
                      [ (λ E → (A → E)) ↓ two-pushouts ]
  two-pushouts-left = codomain-over-equiv _ _

  two-pushouts-right : lift ∘ right == right [ (λ E → (D → E)) ↓ two-pushouts ]
  two-pushouts-right = codomain-over-equiv _ _

  inner-preserve : (k : Pushout d₁) → into (KToL.f k) == left k
  inner-preserve = Pushout-elim
    (λ a → idp)
    (λ c → ! (glue c))
    (λ b → ↓-='-in $ 
      ap left (glue b)
        =⟨ lemma (ap left (glue b)) (glue (g b)) ⟩
      (ap left (glue b) ∙ glue (g b)) ∙' ! (glue (g b))
        =⟨ ! (Into.glue-β b) |in-ctx (λ w → w ∙' ! (glue (g b))) ⟩
      ap into (glue b) ∙' ! (glue (g b))
        =⟨ ! (KToL.glue-β b) |in-ctx (λ w → ap into w ∙' ! (glue (g b))) ⟩
      ap into (ap KToL.f (glue b)) ∙' ! (glue (g b))
        =⟨ ∘-ap into KToL.f (glue b) |in-ctx (λ w → w ∙' ! (glue (g b))) ⟩
      ap (into ∘ KToL.f) (glue b) ∙' ! (glue (g b)) ∎)
    where
    lemma : ∀ {i} {A : Type i} {x y z : A} (p : x == y) (q : y == z)
      → p == (p ∙ q) ∙' ! q
    lemma idp idp = idp

  two-pushouts-inner : lift ∘ KToL.f == left
                       [ (λ E → (Pushout d₁ → E)) ↓ two-pushouts ]
  two-pushouts-inner = codomain-over-equiv _ _ ▹ λ= inner-preserve
    

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

  open TwoPushoutsEquiv (fst f) (fst g) (fst h)
    using (two-pushouts-equiv; inner-preserve)
  module KToL = TwoPushoutsEquiv.KToL (fst f) (fst g) (fst h)

  two-pushouts-ptd : Ptd-Lift {j = lmax l (lmax k (lmax j i))} (Ptd-Pushout ps)
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
      ap (into ∘ lower) (ap lift (! (glue (snd Y))) ∙ idp) ∙ idp
        =⟨ ∙-unit-r _ ⟩
      ap (into ∘ lower) (ap lift (! (glue (snd Y))) ∙ idp)
        =⟨ ∙-unit-r _ |in-ctx (ap (into ∘ lower)) ⟩
      ap (into ∘ lower) (ap lift (! (glue (snd Y))))
        =⟨ ∘-ap (into ∘ lower) lift _ ⟩
      ap into (! (glue (snd Y)))
        =⟨ ap-! into (glue (snd Y)) ⟩
      ! (ap into (glue (snd Y)))
        =⟨ Into.glue-β (snd Y) |in-ctx ! ⟩
      ! (ap left (glue (snd Y)) ∙ glue (g (snd Y)))
        =⟨ !-∙ (ap left (glue (snd Y))) (glue (g (snd Y))) ⟩
      ! (glue (g (snd Y))) ∙ ! (ap left (glue (snd Y)))
        =⟨ !-ap left (glue (snd Y)) |in-ctx (λ w → ! (glue (g (snd Y))) ∙ w) ⟩
      ! (glue (g (snd Y))) ∙ ap left (! (glue (snd Y)))
        =⟨ ∙=∙' (! (glue (g (snd Y)))) (ap left (! (glue (snd Y)))) ⟩
      ! (glue (g (snd Y))) ∙' ap left (! (glue (snd Y))) ∎
      where
      open TwoPushoutsEquiv f g h

  ptd-inner-preserve :
    ((TwoPushoutsEquiv.into (fst f) (fst g) (fst h) ∘ KToL.f) , idp)
    == ptd-left {d = ps₂}
  ptd-inner-preserve = pair= (λ= inner-preserve) $ ↓-app=cst-in $
    ! (∙-unit-r _ ∙ app=-β inner-preserve _)

  two-pushouts-ptd-inner : ptd-lift ∘ptd (KToL.f , idp) == ptd-left {d = ps₂}
    [ (λ V → fst (Ptd-Pushout ps₁ ∙→ V)) ↓ two-pushouts-ptd ]
  two-pushouts-ptd-inner =
    codomain-over-ptd-equiv _ _ _ ▹ ptd-inner-preserve

open TwoPushoutsEquiv 
  using (two-pushouts-equiv; two-pushouts; two-pushouts-left;
         two-pushouts-right; two-pushouts-inner)

open TwoPushoutsPtd
  using (two-pushouts-ptd; two-pushouts-ptd-left; two-pushouts-ptd-right;
         two-pushouts-ptd-inner)
