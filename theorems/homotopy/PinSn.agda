{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.CircleHSpace
open import homotopy.LoopSpaceCircle
import homotopy.Pi2HSusp as Pi2HSusp
open import homotopy.IterSuspensionStable

-- This summerizes all [πₙ Sⁿ]
module homotopy.PinSn where

  πS-SphereS-iso-ℤ : ∀ n → πS n (⊙Sphere (S n)) ≃ᴳ ℤ-group
  πS-SphereS-iso-ℤ 0 =
    πS 0 ⊙S¹
      ≃ᴳ⟨ unTrunc-iso ΩS¹-group-structure ⟩
    Ω^S-group 0 ⊙S¹
      ≃ᴳ⟨ ΩS¹-iso-ℤ ⟩
    ℤ-group
      ≃ᴳ∎
  πS-SphereS-iso-ℤ 1 =
    πS 1 ⊙S²
      ≃ᴳ⟨ Pi2HSusp.π₂-Susp ⊙S¹-hSpace ⟩
    πS 0 ⊙S¹
      ≃ᴳ⟨ πS-SphereS-iso-ℤ O ⟩
    ℤ-group
      ≃ᴳ∎
  πS-SphereS-iso-ℤ (S (S n)) =
    πS (S (S n)) (⊙Sphere (S (S (S n))))
      ≃ᴳ⟨ Susp^StableSucc.stable
           (S n) (S n) (≤-ap-S $ ≤-ap-S $ *2-increasing n)
           (⊙Sphere (S (S n))) {{Sphere-conn (S (S n))}} ⟩
    πS (S n) (⊙Sphere (S (S n)))
      ≃ᴳ⟨ πS-SphereS-iso-ℤ (S n) ⟩
    ℤ-group
      ≃ᴳ∎
