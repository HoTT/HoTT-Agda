{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory

{- Ordinary cohomology groups of the n-torus Tⁿ = (S¹)ⁿ.
 - We have Cᵏ(Tⁿ) == C⁰(S⁰)^(n choose' k) where _choose'_ defined as below.
 - This argument could give Cᵏ((Sᵐ)ⁿ) with a little more work. -}

module cohomology.Torus {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT
open import cohomology.Sphere OT
open import cohomology.SphereProduct cohomology-theory
open import cohomology.Unit cohomology-theory


{- Almost n choose k, but with n choose' O = 0 for any n. -}
_choose'_ : ℕ → ℤ → ℕ
n choose' negsucc _ = 0
n choose' pos O = 0
n choose' pos (S O) = n
O choose' pos (S (S k)) = 0
S n choose' pos (S (S k)) = (n choose' (pos (S (S k)))) + (n choose' (pos (S k)))


_-⊙Torus : ℕ → Ptd₀
O -⊙Torus = ⊙Unit
(S n) -⊙Torus = ⊙S¹ ⊙× (n -⊙Torus)

C-nTorus : (k : ℤ) (n : ℕ)
  → C k (⊙Lift (n -⊙Torus)) ≃ᴳ C 0 (⊙Lift ⊙S⁰) ^ᴳ (n choose' k)

C-nTorus (negsucc k) O = lift-iso ∘eᴳ C-Unit (negsucc k)

C-nTorus (negsucc k) (S n) =
  C (negsucc k) (⊙Lift (S n -⊙Torus))
    ≃ᴳ⟨ C-emap (negsucc k) (⊙lift-equiv ⊙∘e ⊙×-emap (⊙ide _) ⊙lower-equiv) ⟩
  C (negsucc k) (⊙S¹ ⊙× ⊙Lift (n -⊙Torus))
    ≃ᴳ⟨ C-Sphere× (negsucc k) 1 (⊙Lift (n -⊙Torus)) ⟩
  C (negsucc k) (⊙Lift ⊙S¹) ×ᴳ (C (negsucc k) (⊙Lift (n -⊙Torus)) ×ᴳ C (negsucc k) (⊙Susp (⊙Lift (n -⊙Torus))))
    ≃ᴳ⟨ ×ᴳ-emap (C-Sphere-≠ (negsucc k) 1 (ℤ-negsucc≠pos _ _)) (idiso _) ⟩
  0ᴳ ×ᴳ (C (negsucc k) (⊙Lift (n -⊙Torus)) ×ᴳ C (negsucc k) (⊙Susp (⊙Lift (n -⊙Torus))))
    ≃ᴳ⟨ ×ᴳ-unit-l _ ⟩
  C (negsucc k) (⊙Lift (n -⊙Torus)) ×ᴳ C (negsucc k) (⊙Susp (⊙Lift (n -⊙Torus)))
    ≃ᴳ⟨ ×ᴳ-emap
          (lower-iso ∘eᴳ C-nTorus (negsucc k) n)
          (C-nTorus (negsucc (S k)) n ∘eᴳ C-Susp (negsucc (S k)) (⊙Lift (n -⊙Torus))) ⟩
  0ᴳ ×ᴳ Lift-group 0ᴳ
    ≃ᴳ⟨ ×ᴳ-unit-l (Lift-group 0ᴳ) ⟩
  Lift-group 0ᴳ
    ≃ᴳ∎



C-nTorus (pos O) O = lift-iso ∘eᴳ C-Unit 0

C-nTorus (pos O) (S n) =
  C 0 (⊙Lift (S n -⊙Torus))
    ≃ᴳ⟨ C-emap 0 (⊙lift-equiv ⊙∘e ⊙×-emap (⊙ide _) ⊙lower-equiv) ⟩
  C 0 (⊙S¹ ⊙× ⊙Lift (n -⊙Torus))
    ≃ᴳ⟨ C-Sphere× 0 1 (⊙Lift (n -⊙Torus)) ⟩
  C 0 (⊙Lift ⊙S¹) ×ᴳ (C 0 (⊙Lift (n -⊙Torus)) ×ᴳ C 0 (⊙Susp (⊙Lift (n -⊙Torus))))
    ≃ᴳ⟨ ×ᴳ-emap (C-Sphere-≠ 0 1 (pos-≠ (ℕ-O≠S _))) (idiso _) ⟩
  0ᴳ ×ᴳ (C 0 (⊙Lift (n -⊙Torus)) ×ᴳ C 0 (⊙Susp (⊙Lift (n -⊙Torus))))
    ≃ᴳ⟨ ×ᴳ-unit-l _ ⟩
  C 0 (⊙Lift (n -⊙Torus)) ×ᴳ C 0 (⊙Susp (⊙Lift (n -⊙Torus)))
    ≃ᴳ⟨ ×ᴳ-emap
          (lower-iso ∘eᴳ C-nTorus 0 n)
          (C-nTorus -1 n ∘eᴳ C-Susp -1 (⊙Lift (n -⊙Torus))) ⟩
  0ᴳ ×ᴳ Lift-group 0ᴳ
    ≃ᴳ⟨ ×ᴳ-unit-l _ ⟩
  Lift-group 0ᴳ
    ≃ᴳ∎

C-nTorus (pos (S O)) O = lift-iso ∘eᴳ C-Unit 1

C-nTorus (pos (S O)) (S n) = 
  C 1 (⊙Lift (S n -⊙Torus))
    ≃ᴳ⟨ C-emap 1 (⊙lift-equiv ⊙∘e ⊙×-emap (⊙ide _) ⊙lower-equiv) ⟩
  C 1 (⊙S¹ ⊙× ⊙Lift (n -⊙Torus))
    ≃ᴳ⟨ C-Sphere× 1 1 (⊙Lift (n -⊙Torus)) ⟩
  C 1 (⊙Lift ⊙S¹) ×ᴳ (C 1 (⊙Lift (n -⊙Torus)) ×ᴳ C 1 (⊙Susp (⊙Lift (n -⊙Torus))))
    ≃ᴳ⟨ ×ᴳ-emap (C-Sphere-diag 1)
          ( ×ᴳ-unit-r _
        ∘eᴳ ×ᴳ-emap
              (C-nTorus 1 n)
              (lower-iso
                ∘eᴳ C-nTorus 0 n
                ∘eᴳ C-Susp 0 (⊙Lift (n -⊙Torus)))) ⟩
  C 0 (⊙Lift ⊙S⁰) ×ᴳ (C 0 (⊙Lift ⊙S⁰) ^ᴳ n)
    ≃ᴳ∎

C-nTorus (pos (S (S k))) O = lift-iso ∘eᴳ C-Unit (pos (S (S k)))

C-nTorus (pos (S (S k))) (S n) =
  C (pos (S (S k))) (⊙Lift (S n -⊙Torus))
    ≃ᴳ⟨ C-emap (pos (S (S k))) (⊙lift-equiv ⊙∘e ⊙×-emap (⊙ide _) ⊙lower-equiv) ⟩
  C (pos (S (S k))) (⊙S¹ ⊙× ⊙Lift (n -⊙Torus))
    ≃ᴳ⟨ C-Sphere× (pos (S (S k))) 1 (⊙Lift (n -⊙Torus)) ⟩
  C (pos (S (S k))) (⊙Lift ⊙S¹) ×ᴳ (C (pos (S (S k))) (⊙Lift (n -⊙Torus)) ×ᴳ C (pos (S (S k))) (⊙Susp (⊙Lift (n -⊙Torus))))
    ≃ᴳ⟨ ×ᴳ-emap (C-Sphere-≠ (pos (S (S k))) 1 (pos-≠ (ℕ-S-≠ (ℕ-S≠O k)))) (idiso _) ⟩
  0ᴳ ×ᴳ (C (pos (S (S k))) (⊙Lift (n -⊙Torus)) ×ᴳ C (pos (S (S k))) (⊙Susp (⊙Lift (n -⊙Torus))))
    ≃ᴳ⟨ ×ᴳ-unit-l _ ⟩
  C (pos (S (S k))) (⊙Lift (n -⊙Torus)) ×ᴳ C (pos (S (S k))) (⊙Susp (⊙Lift (n -⊙Torus)))
    ≃ᴳ⟨ ×ᴳ-emap
        (C-nTorus (pos (S (S k))) n)
        (C-nTorus (pos (S k)) n ∘eᴳ C-Susp (pos (S k)) (⊙Lift (n -⊙Torus))) ⟩
  (C 0 (⊙Lift ⊙S⁰) ^ᴳ (n choose' pos (S (S k)))) ×ᴳ (C 0 (⊙Lift ⊙S⁰) ^ᴳ (n choose' pos (S k)))
    ≃ᴳ⟨ ^ᴳ-+ (C 0 (⊙Lift ⊙S⁰)) (n choose' pos (S (S k))) (n choose' pos (S k)) ⁻¹ᴳ ⟩
  C 0 (⊙Lift ⊙S⁰) ^ᴳ (S n choose' pos (S (S k)))
    ≃ᴳ∎
