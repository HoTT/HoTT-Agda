{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.elims.SuspSmash

-- (ΣX)∧Y ≃ Σ(X∧Y)

module homotopy.SuspSmash2 where

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  private
    x₀ = pt X
    y₀ = pt Y

  module _ (y : de⊙ Y) where
    module Σ∧-out-smin =
      SuspRec
        {C = Susp (X ∧ Y)}
        north
        south
        (λ x → merid (smin x y))

  Σ∧-out-smgluel-merid : ∀ (x : de⊙ X) →
    idp == ap (Σ∧-out-smin.f y₀) (glue x) ∙ ! (merid (smin x₀ y₀))
  Σ∧-out-smgluel-merid x = ↯ $
    idp
      =⟪ ! (!-inv-r (merid (smin x₀ y₀))) ⟫
    merid (smin x₀ y₀) ∙ ! (merid (smin x₀ y₀))
      =⟪ ! $ ap (_∙ ! (merid (smin (pt X) (pt Y))))
                (Σ∧-out-smin.merid-β (pt Y) x ∙ ap merid (∧-norm-l x)) ⟫
    ap (Σ∧-out-smin.f y₀) (glue x) ∙ ! (merid (smin x₀ y₀)) ∎∎

  Σ∧-out : ⊙Susp (de⊙ X) ∧ Y → Susp (X ∧ Y)
  Σ∧-out =
    Smash-rec
      {C = Susp (X ∧ Y)}
      (λ sx y → Σ∧-out-smin.f y sx)
      north
      north
      (Susp-elim
        {P = λ sx → Susp-rec north south (λ x → merid (smin x y₀)) sx == north}
        idp
        (! (merid (smin x₀ y₀)))
        (λ x → ↓-app=cst-in (Σ∧-out-smgluel-merid x)))
      (λ y → idp)

  ⊙Σ∧-out : ⊙Susp (de⊙ X) ⊙∧ Y ⊙→ ⊙Susp (X ∧ Y)
  ⊙Σ∧-out = Σ∧-out , idp

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

  ⊙∧Σ-out : X ⊙∧ ⊙Susp (de⊙ Y) ⊙→ ⊙Susp (X ∧ Y)
  ⊙∧Σ-out = ⊙Susp-fmap (∧-swap Y X) ⊙∘
            ⊙Σ∧-out Y X ⊙∘
            ⊙∧-swap X (⊙Susp (de⊙ Y))

  ∧Σ-out : X ∧ ⊙Susp (de⊙ Y) → Susp (X ∧ Y)
  ∧Σ-out = fst ⊙∧Σ-out -- Susp-fmap (∧-swap Y X) ∘ Σ∧-out Y X ∘ ∧-swap X (⊙Susp Y)

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
