{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.CircleHSpace
open import homotopy.LoopSpaceCircle
open import homotopy.Pi2HSusp
open import homotopy.IterSuspensionStable

-- This summerizes all [πₙ Sⁿ]
module homotopy.PinSn where

  private
    π1S¹-iso-ℤ : πS 0 ⊙S¹ ≃ᴳ ℤ-group
    π1S¹-iso-ℤ = ΩS¹-iso-ℤ ∘eᴳ unTrunc-iso ΩS¹-group-structure ΩS¹-is-set

  private
    πS-SphereS'-iso-ℤ : ∀ n → πS n (⊙Susp^ n ⊙S¹) ≃ᴳ ℤ-group
    πS-SphereS'-iso-ℤ 0 = π1S¹-iso-ℤ
    πS-SphereS'-iso-ℤ 1 =
      πS 1 ⊙S²
        ≃ᴳ⟨ Pi2HSusp.π₂-Susp S¹-level S¹-conn ⊙S¹-hSpace ⟩
      πS 0 ⊙S¹
        ≃ᴳ⟨ πS-SphereS'-iso-ℤ O ⟩
      ℤ-group
        ≃ᴳ∎
    πS-SphereS'-iso-ℤ (S (S n)) =
      πS (S (S n)) (⊙Susp^ (S (S n)) ⊙S¹)
        ≃ᴳ⟨ Susp^StableSucc.stable ⊙S¹ S¹-conn
             (S n) (S n) (≤-ap-S $ ≤-ap-S $ *2-increasing n) ⟩
      πS (S n) (⊙Susp^ (S n) ⊙S¹)
        ≃ᴳ⟨ πS-SphereS'-iso-ℤ (S n) ⟩
      ℤ-group
        ≃ᴳ∎

  πS-SphereS-iso-ℤ : ∀ n → πS n (⊙Sphere (S n)) ≃ᴳ ℤ-group
  πS-SphereS-iso-ℤ n = πS-SphereS'-iso-ℤ n
                   ∘eᴳ πS-emap n (⊙Susp^-Susp-split-iso n ⊙S⁰)
