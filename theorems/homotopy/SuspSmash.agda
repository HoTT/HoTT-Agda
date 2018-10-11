{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.elims.SuspSmash

-- (ΣX)∧Y ≃ Σ(X∧Y)

module homotopy.SuspSmash where

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  private
    x₀ = pt X
    y₀ = pt Y

  module Σ∧-out-smin (y : de⊙ Y) =
    SuspRec
      {C = Susp (X ∧ Y)}
      north
      south
      (λ x → merid (smin x y))

  Σ∧-out-smgluel-merid : ∀ (x : de⊙ X) →
    Square idp
           (ap (Σ∧-out-smin.f y₀) (merid x))
           (ap (λ sx → north) (merid x))
           (! (merid (smin x₀ y₀)))
  Σ∧-out-smgluel-merid x =
    ((Σ∧-out-smin.merid-β y₀ x ∙ ap merid (∧-norm-l x)) ∙v⊡
     tr-square (merid (smin x₀ y₀))) ⊡v∙
    ! (ap-cst north (merid x))

  module Σ∧OutSmgluel =
    SuspPathElim
      (Σ∧-out-smin.f y₀)
      (λ sx → north)
      idp
      (! (merid (smin x₀ y₀)))
      Σ∧-out-smgluel-merid

  module Σ∧Out =
    SmashRec {X = ⊙Susp (de⊙ X)} {Y = Y}
      {C = Susp (X ∧ Y)}
      (λ sx y → Σ∧-out-smin.f y sx)
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
  Σ∧-out-∧-norm-r y =
    ap Σ∧-out (∧-norm-r y)
      =⟨ ap-∙ Σ∧-out (smgluer y) (! (smgluer y₀)) ⟩
    ap Σ∧-out (smgluer y) ∙ ap Σ∧-out (! (smgluer y₀))
      =⟨ ap2 _∙_
             (Σ∧Out.smgluer-β y)
             (ap-! Σ∧-out (smgluer y₀) ∙
              ap ! (Σ∧Out.smgluer-β y₀)) ⟩
    idp =∎

  module ∧Σ-out-smin (x : de⊙ X) =
    SuspRec
      {C = Susp (X ∧ Y)}
      north
      south
      (λ y → merid (smin x y))

  ∧Σ-out-smgluer-merid : ∀ (y : de⊙ Y) →
    Square idp
           (ap (λ sy → ∧Σ-out-smin.f x₀ sy) (merid y))
           (ap (λ sy → north) (merid y))
           (! (merid (smin x₀ y₀)))
  ∧Σ-out-smgluer-merid y =
    ((∧Σ-out-smin.merid-β x₀ y ∙ ap merid (∧-norm-r y)) ∙v⊡
     tr-square (merid (smin x₀ y₀))) ⊡v∙
    ! (ap-cst north (merid y))

  module ∧ΣOutSmgluer =
    SuspPathElim
      (λ sy → ∧Σ-out-smin.f x₀ sy)
      (λ sy → north)
      idp
      (! (merid (smin x₀ y₀)))
      ∧Σ-out-smgluer-merid

  module ∧ΣOut =
    SmashRec {X = X} {Y = ⊙Susp (de⊙ Y)}
      {C = Susp (X ∧ Y)}
      (λ x sy → ∧Σ-out-smin.f x sy)
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
  ∧Σ-out-∧-norm-l x =
    ap ∧Σ-out (∧-norm-l x)
      =⟨ ap-∙ ∧Σ-out (smgluel x) (! (smgluel x₀)) ⟩
    ap ∧Σ-out (smgluel x) ∙ ap ∧Σ-out (! (smgluel x₀))
      =⟨ ap2 _∙_
             (∧ΣOut.smgluel-β x)
             (ap-! ∧Σ-out (smgluel x₀) ∙
              ap ! (∧ΣOut.smgluel-β x₀)) ⟩
    idp =∎

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
                            smbasel
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

  Σ^∧-out : (n : ℕ) → ⊙Susp^ n X ∧ Y → Susp^ n (X ∧ Y)
  Σ^∧-out O = idf _
  Σ^∧-out (S n) = Susp-fmap (Σ^∧-out n) ∘ Σ∧-out (⊙Susp^ n X) Y

  ⊙Σ^∧-out : (n : ℕ) → ⊙Susp^ n X ⊙∧ Y ⊙→ ⊙Susp^ n (X ⊙∧ Y)
  ⊙Σ^∧-out O = ⊙idf _
  ⊙Σ^∧-out (S n) = ⊙Susp-fmap (Σ^∧-out n) ⊙∘ ⊙Σ∧-out (⊙Susp^ n X) Y

  ∧Σ^-out : (n : ℕ) → X ∧ ⊙Susp^ n Y → Susp^ n (X ∧ Y)
  ∧Σ^-out O = idf _
  ∧Σ^-out (S n) = Susp-fmap (∧Σ^-out n) ∘ ∧Σ-out X (⊙Susp^ n Y)

  ⊙∧Σ^-out : (n : ℕ) → X ⊙∧ ⊙Susp^ n Y ⊙→ ⊙Susp^ n (X ⊙∧ Y)
  ⊙∧Σ^-out O = ⊙idf _
  ⊙∧Σ^-out (S n) = ⊙Susp-fmap (∧Σ^-out n) ⊙∘ ⊙∧Σ-out X (⊙Susp^ n Y)

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  ⊙Σ^∧Σ^-out : ∀ (n m : ℕ) → ⊙Susp^ n X ⊙∧ ⊙Susp^ m Y ⊙→ ⊙Susp^ (n + m) (X ⊙∧ Y)
  ⊙Σ^∧Σ^-out n m =
    ⊙coe (⊙Susp^-+ n m {X ⊙∧ Y}) ⊙∘
    ⊙Susp^-fmap n (⊙∧Σ^-out X Y m) ⊙∘
    ⊙Σ^∧-out X (⊙Susp^ m Y) n

  Σ^∧Σ^-out : ∀ (n m : ℕ) → ⊙Susp^ n X ∧ ⊙Susp^ m Y → Susp^ (n + m) (X ∧ Y)
  Σ^∧Σ^-out n m = fst (⊙Σ^∧Σ^-out n m)
