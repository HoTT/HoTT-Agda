{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.elims.SuspSmash

-- (ΣX)∧Y ≃ Σ(X∧Y)

module homotopy.SuspSmash where

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  private
    x₀ = pt X
    y₀ = pt Y

  Σ∧-out-smgluel-merid : ∀ (x : de⊙ X) →
    Square idp
           (ap (Susp-fmap (λ x' → smin x' y₀)) (merid x))
           (ap (λ sx → north) (merid x))
           (! (merid (smin x₀ y₀)))
  Σ∧-out-smgluel-merid x =
    ((SuspFmap.merid-β (λ x' → smin x' y₀) x ∙ ap merid (∧-norm-l x)) ∙v⊡
     tr-square (merid (smin x₀ y₀))) ⊡v∙
    ! (ap-cst north (merid x))

  module Σ∧OutSmgluel =
    SuspPathElim
      (Susp-fmap (λ x' → smin x' y₀))
      (λ sx → north)
      idp
      (! (merid (smin x₀ y₀)))
      Σ∧-out-smgluel-merid

  module Σ∧Out =
    SmashRec {X = ⊙Susp (de⊙ X)} {Y = Y}
      {C = Susp (X ∧ Y)}
      (λ sx y → Susp-fmap (λ x → smin x y) sx)
      north
      north
      Σ∧OutSmgluel.f
      (λ y → idp)

  Σ∧-out : ⊙Susp (de⊙ X) ∧ Y → Susp (X ∧ Y)
  Σ∧-out = Σ∧Out.f

  ⊙Σ∧-out : ⊙Susp (de⊙ X) ⊙∧ Y ⊙→ ⊙Susp (X ∧ Y)
  ⊙Σ∧-out = Σ∧-out , idp

  Σ∧-out-∧-norm-r : ∀ (y : de⊙ Y) →
    ap Σ∧-out (∧-norm-r y) == idp
  Σ∧-out-∧-norm-r y = Σ∧Out.∧-norm-r-β y

  ∧Σ-out-smgluer-merid : ∀ (y : de⊙ Y) →
    Square idp
           (ap (λ sy → Susp-fmap (smin x₀) sy) (merid y))
           (ap (λ sy → north) (merid y))
           (! (merid (smin x₀ y₀)))
  ∧Σ-out-smgluer-merid y =
    ((SuspFmap.merid-β (smin x₀) y ∙ ap merid (∧-norm-r y)) ∙v⊡
     tr-square (merid (smin x₀ y₀))) ⊡v∙
    ! (ap-cst north (merid y))

  module ∧ΣOutSmgluer =
    SuspPathElim
      (λ sy → Susp-fmap (smin x₀) sy)
      (λ sy → north)
      idp
      (! (merid (smin x₀ y₀)))
      ∧Σ-out-smgluer-merid

  module ∧ΣOut =
    SmashRec {X = X} {Y = ⊙Susp (de⊙ Y)}
      {C = Susp (X ∧ Y)}
      (λ x sy → Susp-fmap (smin x) sy)
      north
      north
      (λ x → idp)
      ∧ΣOutSmgluer.f

  ∧Σ-out : X ∧ ⊙Susp (de⊙ Y) → Susp (X ∧ Y)
  ∧Σ-out = ∧ΣOut.f

  ⊙∧Σ-out : X ⊙∧ ⊙Susp (de⊙ Y) ⊙→ ⊙Susp (X ∧ Y)
  ⊙∧Σ-out = ∧Σ-out , idp

  ∧Σ-out-∧-norm-l : ∀ (x : de⊙ X) →
    ap ∧Σ-out (∧-norm-l x) == idp
  ∧Σ-out-∧-norm-l x = ∧ΣOut.∧-norm-l-β x

  Σ∧-in-merid-smin : de⊙ X → de⊙ Y → pt (⊙Susp (de⊙ X) ⊙∧ Y) == pt (⊙Susp (de⊙ X) ⊙∧ Y)
  Σ∧-in-merid-smin x y = ↯ $
    smin north y₀
      =⟪ ! (∧-norm-r y) ⟫
    smin north y
      =⟪ ap (λ sx → smin sx y) (merid x ∙ ! (merid x₀)) ⟫
    smin north y
      =⟪ ∧-norm-r y ⟫
    smin north y₀ ∎∎

  Σ∧-in-merid-smgluel : ∀ (x : de⊙ X) → Σ∧-in-merid-smin x y₀ == idp
  Σ∧-in-merid-smgluel x = ↯ $
    Σ∧-in-merid-smin x y₀
      =⟪ ap (λ u → ! u ∙ ap (λ sx → smin sx y₀) (merid x ∙ ! (merid x₀)) ∙ u)
            (!-inv-r (smgluer y₀)) ⟫
    ap (λ sx → smin sx y₀) (merid x ∙ ! (merid x₀)) ∙ idp
      =⟪ ap (_∙ idp) $
         homotopy-to-cst-ap (λ sx → smin sx y₀)
                            smgluel
                            (merid x ∙ ! (merid x₀)) ⟫
    (smgluel north ∙ ! (smgluel north)) ∙ idp
      =⟪ ap (_∙ idp) (!-inv-r (smgluel north)) ⟫
    idp ∎∎

  Σ∧-in-merid-smgluer : ∀ (y : de⊙ Y) → Σ∧-in-merid-smin x₀ y == idp
  Σ∧-in-merid-smgluer y = ↯ $
    Σ∧-in-merid-smin x₀ y
      =⟪ ap (λ p → ! (∧-norm-r y) ∙ ap (λ sx → smin sx y) p ∙ ∧-norm-r y)
            (!-inv-r (merid x₀)) ⟫
    ! (∧-norm-r y) ∙ ∧-norm-r y
      =⟪ !-inv-l (∧-norm-r y) ⟫
    idp ∎∎

  Σ∧-in : Susp (X ∧ Y) → ⊙Susp (de⊙ X) ∧ Y
  Σ∧-in =
    Susp-rec
      {C = ⊙Susp (de⊙ X) ∧ Y}
      (smin north y₀)
      (smin north y₀)
      (Smash-rec
        {C = smin north y₀ == smin north y₀}
        Σ∧-in-merid-smin
        idp
        idp
        Σ∧-in-merid-smgluel
        Σ∧-in-merid-smgluer)

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  private
    x₀ = pt X
    y₀ = pt Y

    ∧-swap-∧Σ-out-merid : ∀ (x : de⊙ X) (y : de⊙ Y) →
      ap (Susp-fmap (∧-swap X Y) ∘ Susp-fmap (smin x)) (merid y) =-=
      merid (smin y x)
    ∧-swap-∧Σ-out-merid x y =
      ap (Susp-fmap (∧-swap X Y) ∘ Susp-fmap (smin x)) (merid y)
        =⟪ ap-∘ (Susp-fmap (∧-swap X Y)) (Susp-fmap (smin x)) (merid y) ⟫
      ap (Susp-fmap (∧-swap X Y)) (ap (Susp-fmap (smin x)) (merid y))
        =⟪ ap (ap (Susp-fmap (∧-swap X Y))) (SuspFmap.merid-β (smin x) y) ⟫
      ap (Susp-fmap (∧-swap X Y)) (merid (smin x y))
        =⟪ SuspFmap.merid-β (∧-swap X Y) (smin x y) ⟫
      merid (smin y x) ∎∎

    module Σ∧-∧Σ-swap-smin (x : de⊙ X) =
      SuspPathElim
        (Susp-fmap (∧-swap X Y) ∘ Susp-fmap (smin x))
        (Susp-fmap (λ y → smin y x))
        idp
        idp
        (λ y → ↯ (∧-swap-∧Σ-out-merid x y) ∙v⊡ vid-square ⊡v∙ ! (SuspFmap.merid-β (λ y' → smin y' x) y))

    ∧-swap-∧Σ-out-smgluel : ∀ x →
      ap (Susp-fmap (∧-swap X Y) ∘ ∧Σ-out X Y) (smgluel x) == idp
    ∧-swap-∧Σ-out-smgluel x =
      ap (Susp-fmap (∧-swap X Y) ∘ ∧Σ-out X Y) (smgluel x)
        =⟨ ap-∘ (Susp-fmap (∧-swap X Y)) (∧Σ-out X Y) (smgluel x) ⟩
      ap (Susp-fmap (∧-swap X Y)) (ap (∧Σ-out X Y) (smgluel x))
        =⟨ ap (ap (Susp-fmap (∧-swap X Y))) (∧ΣOut.smgluel-β X Y x) ⟩
      idp =∎

    Σ∧-out-∧-swap-smgluel : ∀ x →
      ap (Σ∧-out Y X ∘ ∧-swap X (⊙Susp (de⊙ Y))) (smgluel x) == idp
    Σ∧-out-∧-swap-smgluel x =
      ap (Σ∧-out Y X ∘ ∧-swap X (⊙Susp (de⊙ Y))) (smgluel x)
        =⟨ ap-∘ (Σ∧-out Y X) (∧-swap X (⊙Susp (de⊙ Y))) (smgluel x) ⟩
      ap (Σ∧-out Y X) (ap (∧-swap X (⊙Susp (de⊙ Y))) (smgluel x))
        =⟨ ap (ap (Σ∧-out Y X)) (SmashSwap.smgluel-β X (⊙Susp (de⊙ Y)) x) ⟩
      ap (Σ∧-out Y X) (∧-norm-r x)
        =⟨ Σ∧-out-∧-norm-r Y X x ⟩
      idp =∎

    ∧-swap-∧Σ-out-smgluer : ∀ sy →
      ap (Susp-fmap (∧-swap X Y) ∘ ∧Σ-out X Y) (smgluer sy) ==
      ap (Susp-fmap (∧-swap X Y)) (∧ΣOutSmgluer.f X Y sy)
    ∧-swap-∧Σ-out-smgluer sy =
      ap (Susp-fmap (∧-swap X Y) ∘ ∧Σ-out X Y) (smgluer sy)
        =⟨ ap-∘ (Susp-fmap (∧-swap X Y)) (∧Σ-out X Y) (smgluer sy) ⟩
      ap (Susp-fmap (∧-swap X Y)) (ap (∧Σ-out X Y) (smgluer sy))
        =⟨ ap (ap (Susp-fmap (∧-swap X Y))) (∧ΣOut.smgluer-β X Y sy) ⟩
      ap (Susp-fmap (∧-swap X Y)) (∧ΣOutSmgluer.f X Y sy) =∎

    Σ∧-out-∧-swap-smgluer : ∀ sy →
      ap (Σ∧-out Y X ∘ ∧-swap X (⊙Susp (de⊙ Y))) (smgluer sy) == Σ∧OutSmgluel.f Y X sy
    Σ∧-out-∧-swap-smgluer sy =
      ap (Σ∧-out Y X ∘ ∧-swap X (⊙Susp (de⊙ Y))) (smgluer sy)
        =⟨ ap-∘ (Σ∧-out Y X) (∧-swap X (⊙Susp (de⊙ Y))) (smgluer sy) ⟩
      ap (Σ∧-out Y X) (ap (∧-swap X (⊙Susp (de⊙ Y))) (smgluer sy))
        =⟨ ap (ap (Σ∧-out Y X)) (SmashSwap.smgluer-β X (⊙Susp (de⊙ Y)) sy) ⟩
      ap (Σ∧-out Y X) (∧-norm-l sy)
        =⟨ Σ∧Out.∧-norm-l-β Y X sy ⟩
      Σ∧OutSmgluel.f Y X sy ∙ idp
        =⟨ ∙-unit-r (Σ∧OutSmgluel.f Y X sy) ⟩
      Σ∧OutSmgluel.f Y X sy =∎

    Σ∧-∧Σ-swap-smgluer-merid : ∀ y →
      Cube ids
           ((ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
             ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))
            ∙v⊡ vid-square)
           (natural-square (Σ∧-∧Σ-swap-smin.f x₀) (merid y))
           (natural-square (ap (Susp-fmap (∧-swap X Y)) ∘ ∧ΣOutSmgluer.f X Y) (merid y))
           (natural-square (Σ∧OutSmgluel.f Y X) (merid y))
           (natural-square (λ v → idp) (merid y))
    Σ∧-∧Σ-swap-smgluer-merid y =
      cube-shift-back (! (Σ∧-∧Σ-swap-smin.merid-square-β x₀ y)) $
      custom-cube-∙v⊡
        (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
         ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))
        (↯ (∧-swap-∧Σ-out-merid x₀ y))
        (ap-cst north (merid y)) $
      cube-shift-top (! top-path) $
      custom-cube-⊡v∙
        (! (SuspFmap.merid-β (λ y' → smin y' x₀) y))
        (ap-cst north (merid y)) $
      cube-shift-front (! front-path) $
      cube-shift-bot (! bot-path) $
      custom-cube (ap merid (∧-norm-l y))
      where
      custom-cube-∙v⊡ :
        ∀ {i} {A : Type i} {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
        {p₀₋₀  : a₀₀₀ == a₀₁₀}
        {p₋₀₀ : a₀₀₀ == a₁₀₀}
        {p₋₁₀ : a₀₁₀ == a₁₁₀}
        {p₁₋₀ : a₁₀₀ == a₁₁₀}
        {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left
        {p₀₋₁ : a₀₀₁ == a₀₁₁}
        {p₋₀₁ p₋₀₁' : a₀₀₁ == a₁₀₁} (q₋₀₁ : p₋₀₁' == p₋₀₁)
        {p₋₁₁ : a₀₁₁ == a₁₁₁}
        {p₁₋₁ : a₁₀₁ == a₁₁₁}
        {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right
        {p₀₀₋ p₀₀₋' : a₀₀₀ == a₀₀₁} (q₀₀₋ : p₀₀₋' == p₀₀₋)
        {p₀₁₋ : a₀₁₀ == a₀₁₁}
        {p₁₀₋ p₁₀₋' : a₁₀₀ == a₁₀₁} (q₁₀₋ : p₁₀₋ == p₁₀₋')
        {p₁₁₋ : a₁₁₀ == a₁₁₁}
        {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
        {sq₋₀₋ : Square p₋₀₀ p₀₀₋' p₁₀₋ p₋₀₁'} -- top
        {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
        {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
        → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ ((! q₀₀₋ ∙v⊡ sq₋₀₋ ⊡v∙ q₁₀₋) ⊡h∙ q₋₀₁) sq₋₁₋ (! q₁₀₋ ∙v⊡ sq₁₋₋)
        → Cube sq₋₋₀ (q₋₀₁ ∙v⊡ sq₋₋₁) (q₀₀₋ ∙v⊡ sq₀₋₋) sq₋₀₋ sq₋₁₋ sq₁₋₋
      custom-cube-∙v⊡ idp idp idp c = c
      custom-cube-⊡v∙ : ∀ {i} {A : Type i} {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
        {p₀₋₀  : a₀₀₀ == a₀₁₀}
        {p₋₀₀ : a₀₀₀ == a₁₀₀}
        {p₋₁₀ : a₀₁₀ == a₁₁₀}
        {p₁₋₀ : a₁₀₀ == a₁₁₀}
        {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left
        {p₀₋₁ : a₀₀₁ == a₀₁₁}
        {p₋₀₁ : a₀₀₁ == a₁₀₁}
        {p₋₁₁ : a₀₁₁ == a₁₁₁}
        {p₁₋₁ : a₁₀₁ == a₁₁₁}
        {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right
        {p₀₀₋ : a₀₀₀ == a₀₀₁}
        {p₀₁₋ p₀₁₋' : a₀₁₀ == a₀₁₁} (q₀₁₋ : p₀₁₋ == p₀₁₋')
        {p₁₀₋ : a₁₀₀ == a₁₀₁}
        {p₁₁₋ p₁₁₋' : a₁₁₀ == a₁₁₁} (q₁₁₋ : p₁₁₋ == p₁₁₋')
        {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
        {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
        {sq₋₁₋ : Square p₋₁₀ p₀₁₋' p₁₁₋ p₋₁₁} -- bottom
        {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
        → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ (q₀₁₋ ∙v⊡ sq₋₁₋ ⊡v∙ q₁₁₋) (sq₁₋₋ ⊡v∙ q₁₁₋)
        → Cube sq₋₋₀ sq₋₋₁ (sq₀₋₋ ⊡v∙ q₀₁₋) sq₋₀₋ sq₋₁₋ sq₁₋₋
      custom-cube-⊡v∙ idp idp c = c
      custom-cube : ∀ {i} {A : Type i} {a₀ a₁ : A}
        {p q : a₀ == a₁} (r : p == q)
        → Cube ids
               vid-square
               vid-square
               (r ∙v⊡ tr-square q)
               (r ∙v⊡ tr-square q)
               ids
      custom-cube {p = idp} {q = .idp} r@idp = idc
      top-path :
        (! (↯ (∧-swap-∧Σ-out-merid x₀ y)) ∙v⊡
         natural-square (ap (Susp-fmap (∧-swap X Y)) ∘ ∧ΣOutSmgluer.f X Y) (merid y) ⊡v∙
         ap-cst north (merid y)) ⊡h∙
        (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
         ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))
        ==
        ap merid (∧-norm-l y) ∙v⊡ tr-square (merid (smin y₀ x₀))
      top-path =
        (! (↯ (∧-swap-∧Σ-out-merid x₀ y)) ∙v⊡
         natural-square (ap (Susp-fmap (∧-swap X Y)) ∘ ∧ΣOutSmgluer.f X Y) (merid y) ⊡v∙
         ap-cst north (merid y)) ⊡h∙
        (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
         ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))
          =⟨ ap (λ u → (! (↯ (∧-swap-∧Σ-out-merid x₀ y)) ∙v⊡
                        u ⊡v∙
                        ap-cst north (merid y)) ⊡h∙
                       (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
                        ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))) $
             natural-square-ap (Susp-fmap (∧-swap X Y)) (∧ΣOutSmgluer.f X Y) (merid y) ⟩
        (! (↯ (∧-swap-∧Σ-out-merid x₀ y)) ∙v⊡
         (ap-∘ (Susp-fmap (∧-swap X Y)) (Susp-fmap (smin x₀)) (merid y) ∙v⊡
          ap-square (Susp-fmap (∧-swap X Y)) (natural-square (∧ΣOutSmgluer.f X Y) (merid y)) ⊡v∙
          ∘-ap (Susp-fmap (∧-swap X Y)) (λ _ → north) (merid y)) ⊡v∙
         ap-cst north (merid y)) ⊡h∙
        (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
         ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))
          =⟨ ap (λ u → (! (↯ (∧-swap-∧Σ-out-merid x₀ y)) ∙v⊡
                        u) ⊡h∙
                       (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
                        ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))) $
             ∙v⊡-⊡v∙-comm
               (ap-∘ (Susp-fmap (∧-swap X Y)) (Susp-fmap (smin x₀)) (merid y))
               (ap-square (Susp-fmap (∧-swap X Y)) (natural-square (∧ΣOutSmgluer.f X Y) (merid y)) ⊡v∙
                ∘-ap (Susp-fmap (∧-swap X Y)) (λ _ → north) (merid y))
               (ap-cst north (merid y)) ⟩
        (! (↯ (∧-swap-∧Σ-out-merid x₀ y)) ∙v⊡
         ap-∘ (Susp-fmap (∧-swap X Y)) (Susp-fmap (smin x₀)) (merid y) ∙v⊡
         ap-square (Susp-fmap (∧-swap X Y)) (natural-square (∧ΣOutSmgluer.f X Y) (merid y)) ⊡v∙
         ∘-ap (Susp-fmap (∧-swap X Y)) (λ _ → north) (merid y) ⊡v∙
         ap-cst north (merid y)) ⊡h∙
        (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
         ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))
          =⟨ ap (λ u → (! (↯ (∧-swap-∧Σ-out-merid x₀ y)) ∙v⊡
                        ap-∘ (Susp-fmap (∧-swap X Y)) (Susp-fmap (smin x₀)) (merid y) ∙v⊡
                        u) ⊡h∙
                       (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
                        ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))) $
             ⊡v∙-assoc
               (ap-square (Susp-fmap (∧-swap X Y)) (natural-square (∧ΣOutSmgluer.f X Y) (merid y)))
               (∘-ap (Susp-fmap (∧-swap X Y)) (λ _ → north) (merid y))
               (ap-cst north (merid y)) ⟩
        (! (↯ (∧-swap-∧Σ-out-merid x₀ y)) ∙v⊡
         ap-∘ (Susp-fmap (∧-swap X Y)) (Susp-fmap (smin x₀)) (merid y) ∙v⊡
         ap-square (Susp-fmap (∧-swap X Y)) (natural-square (∧ΣOutSmgluer.f X Y) (merid y)) ⊡v∙
         (∘-ap (Susp-fmap (∧-swap X Y)) (λ _ → north) (merid y) ∙ ap-cst north (merid y))) ⊡h∙
        (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
         ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))
          =⟨ ap (λ u → (! (↯ (∧-swap-∧Σ-out-merid x₀ y)) ∙v⊡
                        ap-∘ (Susp-fmap (∧-swap X Y)) (Susp-fmap (smin x₀)) (merid y) ∙v⊡
                        ap-square (Susp-fmap (∧-swap X Y)) (natural-square (∧ΣOutSmgluer.f X Y) (merid y)) ⊡v∙
                        u) ⊡h∙
                       (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
                        ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))) $
             =ₛ-out $ ap-∘-cst-coh (Susp-fmap (∧-swap X Y)) north (merid y) ⟩
        (! (↯ (∧-swap-∧Σ-out-merid x₀ y)) ∙v⊡
         ap-∘ (Susp-fmap (∧-swap X Y)) (Susp-fmap (smin x₀)) (merid y) ∙v⊡
         ap-square (Susp-fmap (∧-swap X Y)) (natural-square (∧ΣOutSmgluer.f X Y) (merid y)) ⊡v∙
         ap (ap (Susp-fmap (∧-swap X Y))) (ap-cst north (merid y))) ⊡h∙
        (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
         ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))
          =⟨ ap (λ u → u ⊡h∙
                       (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
                        ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))) $ ! $
             ∙v⊡-assoc
               (! (↯ (∧-swap-∧Σ-out-merid x₀ y)))
               (ap-∘ (Susp-fmap (∧-swap X Y)) (Susp-fmap (smin x₀)) (merid y))
               (ap-square (Susp-fmap (∧-swap X Y)) (natural-square (∧ΣOutSmgluer.f X Y) (merid y)) ⊡v∙
                ap (ap (Susp-fmap (∧-swap X Y))) (ap-cst north (merid y))) ⟩
        ((! (↯ (∧-swap-∧Σ-out-merid x₀ y)) ∙
          ap-∘ (Susp-fmap (∧-swap X Y)) (Susp-fmap (smin x₀)) (merid y)) ∙v⊡
         ap-square (Susp-fmap (∧-swap X Y)) (natural-square (∧ΣOutSmgluer.f X Y) (merid y)) ⊡v∙
         ap (ap (Susp-fmap (∧-swap X Y))) (ap-cst north (merid y))) ⊡h∙
        (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
         ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))
          =⟨ ap (λ u → (u ∙v⊡
                        ap-square (Susp-fmap (∧-swap X Y)) (natural-square (∧ΣOutSmgluer.f X Y) (merid y)) ⊡v∙
                        ap (ap (Susp-fmap (∧-swap X Y))) (ap-cst north (merid y))) ⊡h∙
                       (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
                        ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))) $ =ₛ-out $
             ! (↯ (∧-swap-∧Σ-out-merid x₀ y)) ◃∙
             ap-∘ (Susp-fmap (∧-swap X Y)) (Susp-fmap (smin x₀)) (merid y) ◃∎
               =ₛ⟨ 0 & 1 & !-∙-seq $
                   ap-∘ (Susp-fmap (∧-swap X Y)) (Susp-fmap (smin x₀)) (merid y) ◃∙
                   ↯ (tail (∧-swap-∧Σ-out-merid x₀ y)) ◃∎ ⟩
             ! (↯ (tail (∧-swap-∧Σ-out-merid x₀ y))) ◃∙
             ! (ap-∘ (Susp-fmap (∧-swap X Y)) (Susp-fmap (smin x₀)) (merid y)) ◃∙
             ap-∘ (Susp-fmap (∧-swap X Y)) (Susp-fmap (smin x₀)) (merid y) ◃∎
               =ₛ⟨ 1 & 2 & seq-!-inv-l (ap-∘ (Susp-fmap (∧-swap X Y)) (Susp-fmap (smin x₀)) (merid y) ◃∎) ⟩
             ! (↯ (tail (∧-swap-∧Σ-out-merid x₀ y))) ◃∎ ∎ₛ ⟩
        (! (↯ (tail (∧-swap-∧Σ-out-merid x₀ y))) ∙v⊡
         ap-square (Susp-fmap (∧-swap X Y)) (natural-square (∧ΣOutSmgluer.f X Y) (merid y)) ⊡v∙
         ap (ap (Susp-fmap (∧-swap X Y))) (ap-cst north (merid y))) ⊡h∙
        (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
         ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))
          =⟨ ap (λ u → (! (↯ (tail (∧-swap-∧Σ-out-merid x₀ y))) ∙v⊡
                        ap-square (Susp-fmap (∧-swap X Y)) u ⊡v∙
                        ap (ap (Susp-fmap (∧-swap X Y))) (ap-cst north (merid y))) ⊡h∙
                       (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
                        ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))) $
             ∧ΣOutSmgluer.merid-square-β X Y y ⟩
        (! (↯ (tail (∧-swap-∧Σ-out-merid x₀ y))) ∙v⊡
         ap-square (Susp-fmap (∧-swap X Y)) (∧Σ-out-smgluer-merid X Y y) ⊡v∙
         ap (ap (Susp-fmap (∧-swap X Y))) (ap-cst north (merid y))) ⊡h∙
        (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
         ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))
          =⟨ ap (λ u → (! (↯ (tail (∧-swap-∧Σ-out-merid x₀ y))) ∙v⊡
                        u) ⊡h∙
                       (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
                        ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))) $
             ap-square-⊡v∙
               (Susp-fmap (∧-swap X Y))
               (∧Σ-out-smgluer-merid X Y y)
               (ap-cst north (merid y)) ⟩
        (! (↯ (tail (∧-swap-∧Σ-out-merid x₀ y))) ∙v⊡
         ap-square (Susp-fmap (∧-swap X Y))
                   (∧Σ-out-smgluer-merid X Y y ⊡v∙ ap-cst north (merid y))) ⊡h∙
        (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
         ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))
          =⟨ ap (λ u → (! (↯ (tail (∧-swap-∧Σ-out-merid x₀ y))) ∙v⊡
                        ap-square (Susp-fmap (∧-swap X Y)) u) ⊡h∙
                       (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
                        ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))) $
             ∧Σ-out-smgluer-merid X Y y ⊡v∙ ap-cst north (merid y)
               =⟨ ⊡v∙-assoc
                    ((SuspFmap.merid-β (smin x₀) y ∙ ap merid (∧-norm-r y)) ∙v⊡ tr-square (merid (smin x₀ y₀)))
                    (! (ap-cst north (merid y)))
                    (ap-cst north (merid y)) ⟩
             ((SuspFmap.merid-β (smin x₀) y ∙ ap merid (∧-norm-r y)) ∙v⊡
              tr-square (merid (smin x₀ y₀))) ⊡v∙
             (! (ap-cst north (merid y)) ∙ ap-cst north (merid y))
               =⟨ ap (((SuspFmap.merid-β (smin x₀) y ∙ ap merid (∧-norm-r y)) ∙v⊡
                       tr-square (merid (smin x₀ y₀))) ⊡v∙_) $
                  !-inv-l (ap-cst north (merid y)) ⟩
             (SuspFmap.merid-β (smin x₀) y ∙ ap merid (∧-norm-r y)) ∙v⊡
             tr-square (merid (smin x₀ y₀)) =∎ ⟩
        (! (↯ (tail (∧-swap-∧Σ-out-merid x₀ y))) ∙v⊡
         ap-square (Susp-fmap (∧-swap X Y))
                   ((SuspFmap.merid-β (smin x₀) y ∙ ap merid (∧-norm-r y)) ∙v⊡
                    tr-square (merid (smin x₀ y₀)))) ⊡h∙
        (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
         ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))
          =⟨ ap (λ u → (! (↯ (tail (∧-swap-∧Σ-out-merid x₀ y))) ∙v⊡
                        u) ⊡h∙
                       (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
                        ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))) $ ! $
             ap-square-∙v⊡
               (Susp-fmap (∧-swap X Y))
               (SuspFmap.merid-β (smin x₀) y ∙ ap merid (∧-norm-r y))
               (tr-square (merid (smin x₀ y₀))) ⟩
        (! (↯ (tail (∧-swap-∧Σ-out-merid x₀ y))) ∙v⊡
         ap (ap (Susp-fmap (∧-swap X Y))) (SuspFmap.merid-β (smin x₀) y ∙ ap merid (∧-norm-r y)) ∙v⊡
         ap-square (Susp-fmap (∧-swap X Y)) (tr-square (merid (smin x₀ y₀)))) ⊡h∙
        (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
         ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))
          =⟨ ap (_⊡h∙ (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
                       ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))) $ ! $
             ∙v⊡-assoc
               (! (↯ (tail (∧-swap-∧Σ-out-merid x₀ y))))
               (ap (ap (Susp-fmap (∧-swap X Y))) (SuspFmap.merid-β (smin x₀) y ∙ ap merid (∧-norm-r y)))
               (ap-square (Susp-fmap (∧-swap X Y)) (tr-square (merid (smin x₀ y₀)))) ⟩
        ((! (↯ (tail (∧-swap-∧Σ-out-merid x₀ y))) ∙
          ap (ap (Susp-fmap (∧-swap X Y))) (SuspFmap.merid-β (smin x₀) y ∙ ap merid (∧-norm-r y))) ∙v⊡
         ap-square (Susp-fmap (∧-swap X Y)) (tr-square (merid (smin x₀ y₀)))) ⊡h∙
        (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
         ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))
          =⟨ ap (λ u → (u ∙v⊡
                        ap-square (Susp-fmap (∧-swap X Y)) (tr-square (merid (smin x₀ y₀)))) ⊡h∙
                       (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
                        ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))) $ =ₛ-out $
             ! (↯ (tail (∧-swap-∧Σ-out-merid x₀ y))) ◃∙
             ap (ap (Susp-fmap (∧-swap X Y))) (SuspFmap.merid-β (smin x₀) y ∙ ap merid (∧-norm-r y)) ◃∎
               =ₛ⟨ 0 & 1 & !-∙-seq (tail (∧-swap-∧Σ-out-merid x₀ y)) ⟩
             ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y)) ◃∙
             ! (ap (ap (Susp-fmap (∧-swap X Y))) (SuspFmap.merid-β (smin x₀) y)) ◃∙
             ap (ap (Susp-fmap (∧-swap X Y))) (SuspFmap.merid-β (smin x₀) y ∙ ap merid (∧-norm-r y)) ◃∎
               =ₛ⟨ 2 & 1 &
                   ap-seq-∙ (ap (Susp-fmap (∧-swap X Y))) $
                            (SuspFmap.merid-β (smin x₀) y ◃∙ ap merid (∧-norm-r y) ◃∎) ⟩
             ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y)) ◃∙
             ! (ap (ap (Susp-fmap (∧-swap X Y))) (SuspFmap.merid-β (smin x₀) y)) ◃∙
             ap (ap (Susp-fmap (∧-swap X Y))) (SuspFmap.merid-β (smin x₀) y) ◃∙
             ap (ap (Susp-fmap (∧-swap X Y))) (ap merid (∧-norm-r y)) ◃∎
               =ₛ⟨ 1 & 2 & seq-!-inv-l (ap (ap (Susp-fmap (∧-swap X Y))) (SuspFmap.merid-β (smin x₀) y) ◃∎) ⟩
             ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y)) ◃∙
             ap (ap (Susp-fmap (∧-swap X Y))) (ap merid (∧-norm-r y)) ◃∎
               =ₛ₁⟨ 1 & 1 & ∘-ap (ap (Susp-fmap (∧-swap X Y))) merid (∧-norm-r y) ⟩
             ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y)) ◃∙
             ap (ap (Susp-fmap (∧-swap X Y)) ∘ merid) (∧-norm-r y) ◃∎
               =ₛ⟨ !ₛ $ homotopy-naturality
                     (merid ∘ ∧-swap X Y)
                     (ap (Susp-fmap (∧-swap X Y)) ∘ merid)
                     (! ∘ SuspFmap.merid-β (∧-swap X Y))
                     (∧-norm-r y) ⟩
             ap (merid ∘ ∧-swap X Y) (∧-norm-r y) ◃∙
             ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)) ◃∎
               =ₛ₁⟨ 0 & 1 & ap-∘ merid (∧-swap X Y) (∧-norm-r y) ⟩
             ap merid (ap (∧-swap X Y) (∧-norm-r y)) ◃∙
             ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)) ◃∎
               =ₛ₁⟨ 0 & 1 & ap (ap merid) (∧-swap-norm-r-β X Y y) ⟩
             ap merid (∧-norm-l y) ◃∙
             ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)) ◃∎ ∎ₛ ⟩
        ((ap merid (∧-norm-l y) ∙ ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀))) ∙v⊡
         ap-square (Susp-fmap (∧-swap X Y)) (tr-square (merid (smin x₀ y₀)))) ⊡h∙
        (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
         ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))
          =⟨ ∙v⊡-⊡h∙-comm
               (ap merid (∧-norm-l y) ∙ ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))
               (ap-square (Susp-fmap (∧-swap X Y)) (tr-square (merid (smin x₀ y₀))))
               (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
                ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀))) ⟩
        (ap merid (∧-norm-l y) ∙ ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀))) ∙v⊡
        ap-square (Susp-fmap (∧-swap X Y)) (tr-square (merid (smin x₀ y₀))) ⊡h∙
        (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
         ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))
          =⟨ ap ((ap merid (∧-norm-l y) ∙ ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀))) ∙v⊡_) $
             ! $ ⊡h∙-assoc
               (ap-square (Susp-fmap (∧-swap X Y)) (tr-square (merid (smin x₀ y₀))))
               (ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)))
               (ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀))) ⟩
        (ap merid (∧-norm-l y) ∙ ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀))) ∙v⊡
        ap-square (Susp-fmap (∧-swap X Y)) (tr-square (merid (smin x₀ y₀))) ⊡h∙
        ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ⊡h∙
        ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀))
          =⟨ ap (λ u → (ap merid (∧-norm-l y) ∙ ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀))) ∙v⊡
                       u ⊡h∙
                       ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀))) $
             ap-tr-square (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ⟩
        (ap merid (∧-norm-l y) ∙ ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀))) ∙v⊡
        tr-square (ap (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀))) ⊡h∙
        ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀))
          =⟨ ∙v⊡-assoc
               (ap merid (∧-norm-l y))
               (! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)))
               (tr-square (ap (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀))) ⊡h∙
                ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀))) ⟩
        ap merid (∧-norm-l y) ∙v⊡
        ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)) ∙v⊡
        tr-square (ap (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀))) ⊡h∙
        ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀))
          =⟨ ap (ap merid (∧-norm-l y) ∙v⊡_) $
             tr-square-∙v⊡-⊡h∙ (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀)) ⟩
        ap merid (∧-norm-l y) ∙v⊡ tr-square (merid (smin y₀ x₀)) =∎
      front-path :
        (! (ap-cst (north {A = Y ∧ X}) (merid y)) ∙v⊡
         natural-square (λ v → idp) (merid y)) ⊡v∙
        ap-cst north (merid y)
        ==
        ids
      front-path =
        (! (ap-cst (north {A = Y ∧ X}) (merid y)) ∙v⊡
         natural-square (λ v → idp) (merid y)) ⊡v∙
        ap-cst north (merid y)
          =⟨ ∙v⊡-⊡v∙-comm
               (! (ap-cst (north {A = Y ∧ X}) (merid y)))
               (natural-square (λ v → idp) (merid y))
               (ap-cst north (merid y)) ⟩
        ! (ap-cst (north {A = Y ∧ X}) (merid y)) ∙v⊡
        natural-square (λ v → idp) (merid y) ⊡v∙
        ap-cst north (merid y)
          =⟨ natural-square-cst
               north
               north
               (λ v → idp)
               (merid y) ⟩
        disc-to-square (ap (λ v → idp) (merid y))
          =⟨ ap disc-to-square (ap-cst idp (merid y)) ⟩
        ids =∎
      bot-path :
        ! (SuspFmap.merid-β (λ y' → smin y' x₀) y) ∙v⊡
        natural-square (Σ∧OutSmgluel.f Y X) (merid y) ⊡v∙
        ap-cst north (merid y)
        ==
        ap merid (∧-norm-l y) ∙v⊡ tr-square (merid (smin y₀ x₀))
      bot-path =
        ! (SuspFmap.merid-β (λ y' → smin y' x₀) y) ∙v⊡
        natural-square (Σ∧OutSmgluel.f Y X) (merid y) ⊡v∙
        ap-cst north (merid y)
          =⟨ ap (λ u → ! (SuspFmap.merid-β (λ y' → smin y' x₀) y) ∙v⊡ u ⊡v∙ ap-cst north (merid y)) $
             Σ∧OutSmgluel.merid-square-β Y X y ⟩
        ! (SuspFmap.merid-β (λ y' → smin y' x₀) y) ∙v⊡
        Σ∧-out-smgluel-merid Y X y ⊡v∙
        ap-cst north (merid y)
          =⟨ ap (! (SuspFmap.merid-β (λ y' → smin y' x₀) y) ∙v⊡_) $
             ⊡v∙-assoc
               ((SuspFmap.merid-β (λ y' → smin y' x₀) y ∙ ap merid (∧-norm-l y)) ∙v⊡
                tr-square (merid (smin y₀ x₀)))
               (! (ap-cst north (merid y)))
               (ap-cst north (merid y)) ⟩
        ! (SuspFmap.merid-β (λ y' → smin y' x₀) y) ∙v⊡
        ((SuspFmap.merid-β (λ y' → smin y' x₀) y ∙ ap merid (∧-norm-l y)) ∙v⊡
         tr-square (merid (smin y₀ x₀))) ⊡v∙
        (! (ap-cst north (merid y)) ∙ ap-cst north (merid y))
          =⟨ ap (λ u → ! (SuspFmap.merid-β (λ y' → smin y' x₀) y) ∙v⊡
                       ((SuspFmap.merid-β (λ y' → smin y' x₀) y ∙ ap merid (∧-norm-l y)) ∙v⊡
                        tr-square (merid (smin y₀ x₀))) ⊡v∙
                       u) $
             !-inv-l (ap-cst north (merid y)) ⟩
        ! (SuspFmap.merid-β (λ y' → smin y' x₀) y) ∙v⊡
        ((SuspFmap.merid-β (λ y' → smin y' x₀) y ∙ ap merid (∧-norm-l y)) ∙v⊡
         tr-square (merid (smin y₀ x₀)))
          =⟨ ! $ ∙v⊡-assoc
               (! (SuspFmap.merid-β (λ y' → smin y' x₀) y))
               (SuspFmap.merid-β (λ y' → smin y' x₀) y ∙ ap merid (∧-norm-l y))
               (tr-square (merid (smin y₀ x₀))) ⟩
        (! (SuspFmap.merid-β (λ y' → smin y' x₀) y) ∙
         SuspFmap.merid-β (λ y' → smin y' x₀) y ∙
         ap merid (∧-norm-l y)) ∙v⊡
        tr-square (merid (smin y₀ x₀))
          =⟨ ap (_∙v⊡ tr-square (merid (smin y₀ x₀))) $ =ₛ-out $
             ! (SuspFmap.merid-β (λ y' → smin y' x₀) y) ◃∙
             SuspFmap.merid-β (λ y' → smin y' x₀) y ◃∙
             ap merid (∧-norm-l y) ◃∎
               =ₛ⟨ 0 & 2 & seq-!-inv-l (SuspFmap.merid-β (λ y' → smin y' x₀) y ◃∎) ⟩
             ap merid (∧-norm-l y) ◃∎ ∎ₛ ⟩
        ap merid (∧-norm-l y) ∙v⊡ tr-square (merid (smin y₀ x₀)) =∎

    Σ∧-∧Σ-swap-smgluer : ∀ sy →
      Square (Σ∧-∧Σ-swap-smin.f x₀ sy)
             (ap (Susp-fmap (∧-swap X Y)) (∧ΣOutSmgluer.f X Y sy))
             (Σ∧OutSmgluel.f Y X sy)
             idp
    Σ∧-∧Σ-swap-smgluer =
      Susp-elim
        ids
        ((ap-! (Susp-fmap (∧-swap X Y)) (merid (smin x₀ y₀)) ∙
          ap ! (SuspFmap.merid-β (∧-swap X Y) (smin x₀ y₀))) ∙v⊡
         vid-square)
        (λ y → cube-to-↓-square (Σ∧-∧Σ-swap-smgluer-merid y))

  swap-∧Σ-out : Susp-fmap (∧-swap X Y) ∘ ∧Σ-out X Y
              ∼ Σ∧-out Y X ∘ ∧-swap X (⊙Susp (de⊙ Y))
  swap-∧Σ-out =
    Smash-Path-elim
      (Susp-fmap (∧-swap X Y) ∘ ∧Σ-out X Y)
      (Σ∧-out Y X ∘ ∧-swap X (⊙Susp (de⊙ Y)))
      Σ∧-∧Σ-swap-smin.f
      idp
      idp
      (λ x → ∧-swap-∧Σ-out-smgluel x ∙v⊡ ids ⊡v∙ ! (Σ∧-out-∧-swap-smgluel x))
      (λ sy → ∧-swap-∧Σ-out-smgluer sy ∙v⊡
              Σ∧-∧Σ-swap-smgluer sy ⊡v∙
              ! (Σ∧-out-∧-swap-smgluer sy))

  ⊙swap-∧Σ-out : ⊙Susp-fmap (∧-swap X Y) ◃⊙∘ ⊙∧Σ-out X Y ◃⊙idf
                 =⊙∘
                 ⊙Σ∧-out Y X ◃⊙∘ ⊙∧-swap X (⊙Susp (de⊙ Y)) ◃⊙idf
  ⊙swap-∧Σ-out = =⊙∘-in (⊙λ=' swap-∧Σ-out idp)

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  ⊙swap-Σ∧-out : ⊙Susp-fmap (∧-swap X Y) ◃⊙∘ ⊙Σ∧-out X Y ◃⊙idf
                 =⊙∘
                 ⊙∧Σ-out Y X ◃⊙∘ ⊙∧-swap (⊙Susp (de⊙ X)) Y ◃⊙idf
  ⊙swap-Σ∧-out =
    ⊙Susp-fmap (∧-swap X Y) ◃⊙∘ ⊙Σ∧-out X Y ◃⊙idf
      =⊙∘⟨ 2 & 0 & !⊙∘ $ ⊙∧-swap-inv (⊙Susp (de⊙ X)) Y ⟩
    ⊙Susp-fmap (∧-swap X Y) ◃⊙∘
    ⊙Σ∧-out X Y ◃⊙∘
    ⊙∧-swap Y (⊙Susp (de⊙ X)) ◃⊙∘
    ⊙∧-swap (⊙Susp (de⊙ X)) Y ◃⊙idf
      =⊙∘⟨ 1 & 2 & !⊙∘ (⊙swap-∧Σ-out Y X) ⟩
    ⊙Susp-fmap (∧-swap X Y) ◃⊙∘
    ⊙Susp-fmap (∧-swap Y X) ◃⊙∘
    ⊙∧Σ-out Y X ◃⊙∘
    ⊙∧-swap (⊙Susp (de⊙ X)) Y ◃⊙idf
      =⊙∘⟨ 0 & 2 & !⊙∘ $ =⊙∘-in {fs = ⊙Susp-fmap (∧-swap X Y ∘ ∧-swap Y X) ◃⊙idf} $
                   ⊙Susp-fmap-∘ (∧-swap X Y) (∧-swap Y X) ⟩
    ⊙Susp-fmap (∧-swap X Y ∘ ∧-swap Y X) ◃⊙∘
    ⊙∧Σ-out Y X ◃⊙∘
    ⊙∧-swap (⊙Susp (de⊙ X)) Y ◃⊙idf
      =⊙∘₁⟨ 0 & 1 & ap ⊙Susp-fmap (λ= (∧-swap-inv Y X)) ⟩
    ⊙Susp-fmap (idf _) ◃⊙∘
    ⊙∧Σ-out Y X ◃⊙∘
    ⊙∧-swap (⊙Susp (de⊙ X)) Y ◃⊙idf
      =⊙∘⟨ 0 & 1 & ⊙Susp-fmap-idf (Y ∧ X) ⟩
    ⊙∧Σ-out Y X ◃⊙∘
    ⊙∧-swap (⊙Susp (de⊙ X)) Y ◃⊙idf ∎⊙∘
