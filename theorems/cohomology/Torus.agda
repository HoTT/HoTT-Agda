{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Theory

{- Ordinary cohomology groups of the n-torus Tⁿ = (S¹)ⁿ.
 - We have Cᵏ(Tⁿ) == C⁰(S⁰)^(n choose' k) where _choose'_ defined as below.
 - This argument could give Cᵏ((Sᵐ)ⁿ) with a little more work. -}

module cohomology.Torus {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT
open import cohomology.Sn OT
open import cohomology.SphereProduct cohomology-theory
open import cohomology.Unit cohomology-theory


{- Almost n choose k, but with n choose' O = 0 for any n. -}
_choose'_ : ℕ → ℤ → ℕ
n choose' negsucc _ = 0
n choose' pos O = 0
n choose' pos (S O) = n
O choose' pos (S (S k)) = 0
S n choose' pos (S (S k)) = (n choose' (pos (S (S k)))) + (n choose' (pos (S k)))


_-⊙Torus : ℕ → Ptd i
O -⊙Torus = ⊙Lift ⊙Unit
(S n) -⊙Torus = ⊙Lift {j = i} ⊙S¹ ⊙× (n -⊙Torus)

C-nTorus : (k : ℤ) (n : ℕ)
  → C k (n -⊙Torus) == C 0 (⊙Lift ⊙S⁰) ^ᴳ (n choose' k)

C-nTorus (negsucc k) O = C-Unit (negsucc k)

C-nTorus (negsucc k) (S n) =
  C-Sphere× (negsucc k) 1 (n -⊙Torus)
  ∙ ap (λ K → K ×ᴳ (C (negsucc k) (n -⊙Torus)
                    ×ᴳ C (negsucc k) (⊙Susp^ 1 (n -⊙Torus))))
       (C-Sphere-≠ (negsucc k) 1 (ℤ-negsucc≠pos _ _))
  ∙ ×ᴳ-unit-l {G = C (negsucc k) (n -⊙Torus)
                   ×ᴳ C (negsucc k) (⊙Susp (n -⊙Torus))}
  ∙ ap (λ K → K ×ᴳ C (negsucc k) (⊙Susp (n -⊙Torus)))
       (C-nTorus (negsucc k) n)
  ∙ ×ᴳ-unit-l {G = C (negsucc k) (⊙Susp (n -⊙Torus))}
  ∙ group-ua (C-Susp (negsucc (S k)) (n -⊙Torus))
  ∙ C-nTorus (negsucc (S k)) n

C-nTorus (pos O) O = C-Unit (pos O)

C-nTorus (pos O) (S n) =
  C-Sphere× (pos O) 1 (n -⊙Torus)
  ∙ ap (λ K → K ×ᴳ (C 0 (n -⊙Torus) ×ᴳ C 0 (⊙Susp (n -⊙Torus))))
       (C-Sphere-≠ (pos O) 1 (pos-≠ (ℕ-O≠S _)))
  ∙ ×ᴳ-unit-l {G = C 0 (n -⊙Torus) ×ᴳ C 0 (⊙Susp (n -⊙Torus))}
  ∙ ap (λ K → K ×ᴳ C 0 (⊙Susp (n -⊙Torus)))
       (C-nTorus 0 n)
  ∙ ×ᴳ-unit-l {G = C 0 (⊙Susp (n -⊙Torus))}
  ∙ group-ua (C-Susp (negsucc O) (n -⊙Torus))
  ∙ C-nTorus (negsucc O) n

C-nTorus (pos (S O)) O = C-Unit 1

C-nTorus (pos (S O)) (S n) =
  C-Sphere× 1 1 (n -⊙Torus)
  ∙ ap (λ K → K ×ᴳ (C 1 (n -⊙Torus)
                    ×ᴳ C 1 (⊙Susp (n -⊙Torus))))
       (C-Sphere-diag 1)
  ∙ ap (λ K → C 0 (⊙Lift ⊙S⁰) ×ᴳ K)
       (ap2 _×ᴳ_
         (C-nTorus 1 n)
         (group-ua (C-Susp 0 (n -⊙Torus)) ∙ C-nTorus 0 n)
        ∙ ×ᴳ-unit-r {G = C 0 (⊙Lift ⊙S⁰) ^ᴳ (n choose' 1)})

C-nTorus (pos (S (S k))) O =
  C-Unit (pos (S (S k)))

C-nTorus (pos (S (S k))) (S n) =
  C-Sphere× (pos (S (S k))) 1 (n -⊙Torus)
  ∙ ap (λ K → K ×ᴳ (C (pos (S (S k))) (n -⊙Torus)
                    ×ᴳ C (pos (S (S k))) (⊙Susp (n -⊙Torus))))
       (C-Sphere-≠ (pos (S (S k))) 1 (pos-≠ (ℕ-S-≠ (ℕ-S≠O k))))
  ∙ ×ᴳ-unit-l {G = (C (pos (S (S k))) (n -⊙Torus))
                   ×ᴳ (C (pos (S (S k))) (⊙Susp (n -⊙Torus)))}
  ∙ ap2 _×ᴳ_ (C-nTorus (pos (S (S k))) n)
             (group-ua (C-Susp (pos (S k)) (n -⊙Torus)) ∙ C-nTorus (pos (S k)) n)
  ∙ ^ᴳ-sum (C 0 (⊙Lift ⊙S⁰)) (n choose' pos (S (S k))) (n choose' pos (S k))
