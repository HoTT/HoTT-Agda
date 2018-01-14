{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Paths
open import lib.types.Pointed

module lib.types.CommutingSquare where

{- maps between two functions -}

infix 0 _□$_
_□$_ = CommSquare.commutes

de⊙-csmap : ∀ {i₀ i₁ j₀ j₁}
  {X₀ : Ptd i₀} {X₁ : Ptd i₁}
  {Y₀ : Ptd j₀} {Y₁ : Ptd j₁}
  {f : X₀ ⊙→ Y₀} {g : X₁ ⊙→ Y₁}
  {hX : X₀ ⊙→ X₁} {hY : Y₀ ⊙→ Y₁}
  → ⊙CommSquare f g hX hY
  → CommSquare (fst f) (fst g) (fst hX) (fst hY)
de⊙-csmap (⊙comm-sqr cs) = comm-sqr (fst cs)

CommSquare-∘v : ∀ {i₀ i₁ i₂ j₀ j₁ j₂}
  {A₀ : Type i₀} {A₁ : Type i₁} {A₂ : Type i₂}
  {B₀ : Type j₀} {B₁ : Type j₁} {B₂ : Type j₂}
  {f₀ : A₀ → B₀} {f₁ : A₁ → B₁} {f₂ : A₂ → B₂}
  {hA : A₀ → A₁} {hB : B₀ → B₁}
  {kA : A₁ → A₂} {kB : B₁ → B₂}
  → CommSquare f₁ f₂ kA kB
  → CommSquare f₀ f₁ hA hB
  → CommSquare f₀ f₂ (kA ∘ hA) (kB ∘ hB)
CommSquare-∘v {hA = hA} {kB = kB} (comm-sqr □₁₂) (comm-sqr □₀₁) =
  comm-sqr λ a₀ → ap kB (□₀₁ a₀) ∙ □₁₂ (hA a₀)

{- XXX Reduce the usage of [⊙λ=] -}
⊙CommSquare-∘v : ∀ {i₀ i₁ i₂ j₀ j₁ j₂}
  {X₀ : Ptd i₀} {X₁ : Ptd i₁} {X₂ : Ptd i₂}
  {Y₀ : Ptd j₀} {Y₁ : Ptd j₁} {Y₂ : Ptd j₂}
  {f₀ : X₀ ⊙→ Y₀} {f₁ : X₁ ⊙→ Y₁} {f₂ : X₂ ⊙→ Y₂}
  {hX : X₀ ⊙→ X₁} {hY : Y₀ ⊙→ Y₁}
  {kX : X₁ ⊙→ X₂} {kY : Y₁ ⊙→ Y₂}
  → ⊙CommSquare f₁ f₂ kX kY
  → ⊙CommSquare f₀ f₁ hX hY
  → ⊙CommSquare f₀ f₂ (kX ⊙∘ hX) (kY ⊙∘ hY)
⊙CommSquare-∘v {f₀ = f₀} {f₁} {f₂} {hX} {hY} {kX} {kY} (⊙comm-sqr □₁₂) (⊙comm-sqr □₀₁) =
  ⊙comm-sqr $ ⊙app= $
    (kY ⊙∘ hY) ⊙∘ f₀
      =⟨ ⊙λ= $ ⊙∘-assoc kY hY f₀ ⟩
    kY ⊙∘ (hY ⊙∘ f₀)
      =⟨ ap (kY ⊙∘_) (⊙λ= □₀₁) ⟩
    kY ⊙∘ (f₁ ⊙∘ hX)
      =⟨ ! $ ⊙λ= $ ⊙∘-assoc kY f₁ hX ⟩
    (kY ⊙∘ f₁) ⊙∘ hX
      =⟨ ap (_⊙∘ hX) (⊙λ= □₁₂) ⟩
    (f₂ ⊙∘ kX) ⊙∘ hX
      =⟨ ⊙λ= $ ⊙∘-assoc f₂ kX hX ⟩
    f₂ ⊙∘ (kX ⊙∘ hX)
      =∎

CommSquareEquiv-∘v : ∀ {i₀ i₁ i₂ j₀ j₁ j₂}
  {A₀ : Type i₀} {A₁ : Type i₁} {A₂ : Type i₂}
  {B₀ : Type j₀} {B₁ : Type j₁} {B₂ : Type j₂}
  {f₀ : A₀ → B₀} {f₁ : A₁ → B₁} {f₂ : A₂ → B₂}
  {hA : A₀ → A₁} {hB : B₀ → B₁}
  {kA : A₁ → A₂} {kB : B₁ → B₂}
  → CommSquareEquiv f₁ f₂ kA kB
  → CommSquareEquiv f₀ f₁ hA hB
  → CommSquareEquiv f₀ f₂ (kA ∘ hA) (kB ∘ hB)
CommSquareEquiv-∘v (cs₀ , kA-ise , kB-ise) (cs₁ , hA-ise , hB-ise) =
  (CommSquare-∘v cs₀ cs₁ , kA-ise ∘ise hA-ise , kB-ise ∘ise hB-ise)

⊙CommSquareEquiv-∘v : ∀ {i₀ i₁ i₂ j₀ j₁ j₂}
  {X₀ : Ptd i₀} {X₁ : Ptd i₁} {X₂ : Ptd i₂}
  {Y₀ : Ptd j₀} {Y₁ : Ptd j₁} {Y₂ : Ptd j₂}
  {f₀ : X₀ ⊙→ Y₀} {f₁ : X₁ ⊙→ Y₁} {f₂ : X₂ ⊙→ Y₂}
  {hX : X₀ ⊙→ X₁} {hY : Y₀ ⊙→ Y₁}
  {kX : X₁ ⊙→ X₂} {kY : Y₁ ⊙→ Y₂}
  → ⊙CommSquareEquiv f₁ f₂ kX kY
  → ⊙CommSquareEquiv f₀ f₁ hX hY
  → ⊙CommSquareEquiv f₀ f₂ (kX ⊙∘ hX) (kY ⊙∘ hY)
⊙CommSquareEquiv-∘v (⊙cs₀ , kX-ise , kY-ise) (⊙cs₁ , hX-ise , hY-ise) =
  (⊙CommSquare-∘v ⊙cs₀ ⊙cs₁ , kX-ise ∘ise hX-ise , kY-ise ∘ise hY-ise)

CommSquareEquiv-inverse-v : ∀ {i₀ i₁ j₀ j₁}
  {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
  {f₀ : A₀ → B₀} {f₁ : A₁ → B₁} {hA : A₀ → A₁} {hB : B₀ → B₁}
  → (cse : CommSquareEquiv f₀ f₁ hA hB)
  → CommSquareEquiv f₁ f₀ (is-equiv.g (fst (snd cse))) (is-equiv.g (snd (snd cse)))
CommSquareEquiv-inverse-v {f₀ = f₀} {f₁} {hA} {hB} (comm-sqr □ , hA-ise , hB-ise) =
    comm-sqr (λ a₁ → ap hB.g (! (□ (hA.g a₁) ∙ ap f₁ (hA.f-g a₁))) ∙ hB.g-f (f₀ (hA.g a₁)))
  , is-equiv-inverse hA-ise , is-equiv-inverse hB-ise
  where module hA = is-equiv hA-ise
        module hB = is-equiv hB-ise

CommSquare-inverse-v : ∀ {i₀ i₁ j₀ j₁}
  {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
  {f₀ : A₀ → B₀} {f₁ : A₁ → B₁} {hA : A₀ → A₁} {hB : B₀ → B₁}
  → CommSquare f₀ f₁ hA hB → (hA-ise : is-equiv hA) (hB-ise : is-equiv hB)
  → CommSquare f₁ f₀ (is-equiv.g hA-ise) (is-equiv.g hB-ise)
CommSquare-inverse-v cs hA-ise hB-ise = fst $ CommSquareEquiv-inverse-v (cs , hA-ise , hB-ise)

abstract
  -- 'r' with respect to '∘v'
  CommSquare-inverse-inv-r : ∀ {i₀ i₁ j₀ j₁}
    {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
    {f₀ : A₀ → B₀} {f₁ : A₁ → B₁} {hA : A₀ → A₁} {hB : B₀ → B₁}
    (cs : CommSquare f₀ f₁ hA hB) (hA-ise : is-equiv hA) (hB-ise : is-equiv hB)
    → ∀ a₁ → (CommSquare-∘v cs (CommSquare-inverse-v cs hA-ise hB-ise) □$ a₁)
          == is-equiv.f-g hB-ise (f₁ a₁) ∙ ! (ap f₁ (is-equiv.f-g hA-ise a₁))
  CommSquare-inverse-inv-r {f₀ = f₀} {f₁} {hA} {hB} (comm-sqr □) hA-ise hB-ise a₁ =
    ap hB ( ap hB.g (! (□ (hA.g a₁) ∙ ap f₁ (hA.f-g a₁)))
            ∙ hB.g-f (f₀ (hA.g a₁)))
    ∙ □ (hA.g a₁)
      =⟨ ap-∙ hB (ap hB.g (! (□ (hA.g a₁) ∙ ap f₁ (hA.f-g a₁)))) (hB.g-f (f₀ (hA.g a₁)))
          |in-ctx _∙ □ (hA.g a₁) ⟩
    ( ap hB (ap hB.g (! (□ (hA.g a₁) ∙ ap f₁ (hA.f-g a₁))))
      ∙ ap hB (hB.g-f (f₀ (hA.g a₁))))
    ∙ □ (hA.g a₁)
      =⟨ ap2 _∙_
          (∘-ap hB hB.g (! (□ (hA.g a₁) ∙ ap f₁ (hA.f-g a₁))))
          (hB.adj (f₀ (hA.g a₁)))
          |in-ctx _∙ □ (hA.g a₁) ⟩
    ( ap (hB ∘ hB.g) (! (□ (hA.g a₁) ∙ ap f₁ (hA.f-g a₁)))
      ∙ hB.f-g (hB (f₀ (hA.g a₁))))
    ∙ □ (hA.g a₁)
      =⟨ ! (↓-app=idf-out $ apd hB.f-g (! (□ (hA.g a₁) ∙ ap f₁ (hA.f-g a₁))))
          |in-ctx _∙ □ (hA.g a₁) ⟩
    ( hB.f-g (f₁ a₁)
      ∙' (! (□ (hA.g a₁) ∙ ap f₁ (hA.f-g a₁))))
    ∙ □ (hA.g a₁)
      =⟨ lemma (hB.f-g (f₁ a₁)) (□ (hA.g a₁)) (ap f₁ (hA.f-g a₁)) ⟩
    hB.f-g (f₁ a₁) ∙ ! (ap f₁ (hA.f-g a₁))
      =∎
    where module hA = is-equiv hA-ise
          module hB = is-equiv hB-ise

          lemma : ∀ {i} {A : Type i} {a₀ a₁ a₂ a₃ : A}
            (p₀ : a₀ == a₁) (p₁ : a₃ == a₂) (p₂ : a₂ == a₁)
            → (p₀ ∙' (! (p₁ ∙ p₂))) ∙ p₁ == p₀ ∙ ! p₂
          lemma idp idp idp = idp

  -- 'l' with respect to '∘v'
  CommSquare-inverse-inv-l : ∀ {i₀ i₁ j₀ j₁}
    {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
    {f₀ : A₀ → B₀} {f₁ : A₁ → B₁} {hA : A₀ → A₁} {hB : B₀ → B₁}
    (cs : CommSquare f₀ f₁ hA hB) (hA-ise : is-equiv hA) (hB-ise : is-equiv hB)
    → ∀ a₀ → (CommSquare-∘v (CommSquare-inverse-v cs hA-ise hB-ise) cs □$ a₀)
          == is-equiv.g-f hB-ise (f₀ a₀) ∙ ! (ap f₀ (is-equiv.g-f hA-ise a₀))
  CommSquare-inverse-inv-l {f₀ = f₀} {f₁} {hA} {hB} (comm-sqr □) hA-ise hB-ise a₀ =
    ap hB.g (□ a₀)
    ∙ ( ap hB.g (! (□ (hA.g (hA a₀)) ∙ ap f₁ (hA.f-g (hA a₀))))
        ∙ hB.g-f (f₀ (hA.g (hA a₀))))
      =⟨ ! (hA.adj a₀) |in-ctx ap f₁
          |in-ctx □ (hA.g (hA a₀)) ∙_
          |in-ctx ! |in-ctx ap hB.g
          |in-ctx _∙ hB.g-f (f₀ (hA.g (hA a₀)))
          |in-ctx ap hB.g (□ a₀) ∙_ ⟩
    ap hB.g (□ a₀)
    ∙ ( ap hB.g (! (□ (hA.g (hA a₀)) ∙ ap f₁ (ap hA (hA.g-f a₀))))
        ∙ hB.g-f (f₀ (hA.g (hA a₀))))
      =⟨ ∘-ap f₁ hA (hA.g-f a₀)
          |in-ctx □ (hA.g (hA a₀)) ∙_
          |in-ctx ! |in-ctx ap hB.g
          |in-ctx _∙ hB.g-f (f₀ (hA.g (hA a₀)))
          |in-ctx ap hB.g (□ a₀) ∙_ ⟩
    ap hB.g (□ a₀)
    ∙ ( ap hB.g (! (□ (hA.g (hA a₀)) ∙ ap (f₁ ∘ hA) (hA.g-f a₀)))
        ∙ hB.g-f (f₀ (hA.g (hA a₀))))
      =⟨ ↓-='-out' (apd □ (hA.g-f a₀))
          |in-ctx ! |in-ctx ap hB.g
          |in-ctx _∙ hB.g-f (f₀ (hA.g (hA a₀)))
          |in-ctx ap hB.g (□ a₀) ∙_ ⟩
    ap hB.g (□ a₀)
    ∙ ( ap hB.g (! (ap (hB ∘ f₀) (hA.g-f a₀) ∙' □ a₀))
        ∙ hB.g-f (f₀ (hA.g (hA a₀))))
      =⟨ lemma hB.g (□ a₀) (ap (hB ∘ f₀) (hA.g-f a₀)) (hB.g-f (f₀ (hA.g (hA a₀)))) ⟩
    ! (ap hB.g (ap (hB ∘ f₀) (hA.g-f a₀)))
    ∙' hB.g-f (f₀ (hA.g (hA a₀)))
      =⟨ ∘-ap hB.g (hB ∘ f₀) (hA.g-f a₀)
          |in-ctx ! |in-ctx _∙' hB.g-f (f₀ (hA.g (hA a₀))) ⟩
    ! (ap (hB.g ∘ hB ∘ f₀) (hA.g-f a₀))
    ∙' hB.g-f (f₀ (hA.g (hA a₀)))
      =⟨ !-ap (hB.g ∘ hB ∘ f₀) (hA.g-f a₀)
          |in-ctx _∙' hB.g-f (f₀ (hA.g (hA a₀))) ⟩
    ap (hB.g ∘ hB ∘ f₀) (! (hA.g-f a₀))
    ∙' hB.g-f (f₀ (hA.g (hA a₀)))
      =⟨ ! (↓-='-out' (apd (hB.g-f ∘ f₀) (! (hA.g-f a₀)))) ⟩
    hB.g-f (f₀ a₀) ∙ ap f₀ (! (hA.g-f a₀))
      =⟨ ap-! f₀ (hA.g-f a₀) |in-ctx hB.g-f (f₀ a₀) ∙_ ⟩
    hB.g-f (f₀ a₀) ∙ ! (ap f₀ (hA.g-f a₀))
      =∎
    where module hA = is-equiv hA-ise
          module hB = is-equiv hB-ise

          lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
            {a₀ a₁ a₂ : A} {b : B}
            (p₀ : a₀ == a₁) (p₁ : a₂ == a₀) (q₀ : f a₂ == b)
            → ap f p₀ ∙ (ap f (! (p₁ ∙' p₀)) ∙ q₀) == ! (ap f p₁) ∙' q₀
          lemma f idp idp idp = idp

module _ where

CommSquareEquiv-preserves-equiv : ∀ {i₀ i₁ j₀ j₁}
  {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
  {f₀ : A₀ → B₀} {f₁ : A₁ → B₁} {hA : A₀ → A₁} {hB : B₀ → B₁}
  → CommSquareEquiv f₀ f₁ hA hB
  → is-equiv f₀ → is-equiv f₁
CommSquareEquiv-preserves-equiv {f₀ = f₀} {f₁} {hA} {hB} (cs , hA-ise , hB-ise) f₀-ise =
  ∼-preserves-equiv
    (λ a₁ →
      hB (f₀ (is-equiv.g hA-ise a₁))
        =⟨ cs □$ is-equiv.g hA-ise a₁ ⟩
      f₁ (hA (is-equiv.g hA-ise a₁))
        =⟨ ap f₁ $ is-equiv.f-g hA-ise a₁ ⟩
      f₁ a₁
        =∎)
    (hB-ise ∘ise f₀-ise ∘ise is-equiv-inverse hA-ise)

CommSquareEquiv-preserves'-equiv : ∀ {i₀ i₁ j₀ j₁}
  {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
  {f₀ : A₀ → B₀} {f₁ : A₁ → B₁} {hA : A₀ → A₁} {hB : B₀ → B₁}
  → CommSquareEquiv f₀ f₁ hA hB
  → is-equiv f₁ → is-equiv f₀
CommSquareEquiv-preserves'-equiv {f₀ = f₀} {f₁} {hA} {hB} (cs , hA-ise , hB-ise) f₁-ise =
  ∼-preserves-equiv
    (λ a₀ →
      is-equiv.g hB-ise (f₁ (hA a₀))
        =⟨ ! $ ap (is-equiv.g hB-ise) (cs □$ a₀) ⟩
      is-equiv.g hB-ise (hB (f₀ a₀))
        =⟨ is-equiv.g-f hB-ise (f₀ a₀) ⟩
      f₀ a₀
        =∎)
    (is-equiv-inverse hB-ise ∘ise f₁-ise ∘ise hA-ise)

⊙CommSquareEquiv-preserves-equiv : ∀ {i₀ i₁ j₀ j₁}
  {X₀ : Ptd i₀} {X₁ : Ptd i₁} {Y₀ : Ptd j₀} {Y₁ : Ptd j₁}
  {f₀ : X₀ ⊙→ Y₀} {f₁ : X₁ ⊙→ Y₁} {hX : X₀ ⊙→ X₁} {hY : Y₀ ⊙→ Y₁}
  → ⊙CommSquareEquiv f₀ f₁ hX hY
  → is-equiv (fst f₀) → is-equiv (fst f₁)
⊙CommSquareEquiv-preserves-equiv (⊙cs , ise) =
  CommSquareEquiv-preserves-equiv (de⊙-csmap ⊙cs , ise)

⊙CommSquareEquiv-preserves'-equiv : ∀ {i₀ i₁ j₀ j₁}
  {X₀ : Ptd i₀} {X₁ : Ptd i₁} {Y₀ : Ptd j₀} {Y₁ : Ptd j₁}
  {f₀ : X₀ ⊙→ Y₀} {f₁ : X₁ ⊙→ Y₁} {hX : X₀ ⊙→ X₁} {hY : Y₀ ⊙→ Y₁}
  → ⊙CommSquareEquiv f₀ f₁ hX hY
  → is-equiv (fst f₁) → is-equiv (fst f₀)
⊙CommSquareEquiv-preserves'-equiv (⊙cs , ise) =
  CommSquareEquiv-preserves'-equiv (de⊙-csmap ⊙cs , ise)
