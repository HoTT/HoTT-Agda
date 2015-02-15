{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Theory

{- Cohomology groups of the n-torus (S¹)ⁿ.
 - We have Ĉᵏ(Tⁿ) == C⁰(S⁰)^(n choose' k) where _choose'_ defined as below.
 - This argument could give Cᵏ((Sᵐ)ⁿ) with a little more work. -}

module cohomology.Torus {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT
open import cohomology.Sn OT
open import cohomology.SphereProduct cohomology-theory
open import cohomology.Unit cohomology-theory


{- Almost n choose k, but with n choose' O = 0 for any n. -}
_choose'_ : ℕ → ℤ → ℕ
n choose' (neg _) = 0
n choose' O = 0
n choose' pos O = n
O choose' (pos (S k)) = 0
S n choose' pos (S k) = (n choose' (pos k)) + (n choose' (pos (S k)))


_-⊙Torus : ℕ → Ptd i
O -⊙Torus = ⊙Lift ⊙Unit
(S n) -⊙Torus = (⊙Sphere {i} 1) ⊙× (n -⊙Torus)

C-nTorus : (k : ℤ) (n : ℕ)
  → C k (n -⊙Torus) == (C O (⊙Sphere 0)) ^ᴳ (n choose' k)

C-nTorus (neg k) O = C-Unit-is-trivial (neg k)

C-nTorus (neg k) (S n) =
  C-Sphere× (neg k) 1 (n -⊙Torus)
  ∙ ap (λ K → K ×ᴳ (C (neg k) (⊙Susp^ 1 (n -⊙Torus))
                    ×ᴳ C (neg k) (n -⊙Torus)))
       (C-Sphere-≠ (neg k) 1 (ℤ-neg≠pos _ _))
  ∙ ×ᴳ-unit-l {G = C (neg k) (⊙Susp (n -⊙Torus))
                   ×ᴳ C (neg k) (n -⊙Torus)}
  ∙ ap (λ K → C (neg k) (⊙Susp (n -⊙Torus)) ×ᴳ K)
        (C-nTorus (neg k) n)
  ∙ ×ᴳ-unit-r {G = C (neg k) (⊙Susp (n -⊙Torus))}
  ∙ C-Susp (neg (S k)) (n -⊙Torus)
  ∙ C-nTorus (neg (S k)) n

C-nTorus O O = C-Unit-is-trivial O

C-nTorus O (S n) =
  C-Sphere× O 1 (n -⊙Torus)
  ∙ ap (λ K → K ×ᴳ (C O (⊙Susp (n -⊙Torus)) ×ᴳ C O (n -⊙Torus)))
       (C-Sphere-≠ O 1 (ℤ-O≠pos _))
  ∙ ×ᴳ-unit-l {G = C O (⊙Susp (n -⊙Torus)) ×ᴳ C O (n -⊙Torus)}
  ∙ ap (λ K → C O (⊙Susp (n -⊙Torus)) ×ᴳ K)
       (C-nTorus O n)
  ∙ ×ᴳ-unit-r {G = C O (⊙Susp (n -⊙Torus))}
  ∙ C-Susp (neg O) (n -⊙Torus)
  ∙ C-nTorus (neg O) n

C-nTorus (pos O) O =
  C-Unit-is-trivial (pos O)

C-nTorus (pos O) (S n) =
  C-Sphere× (pos O) 1 (n -⊙Torus)
  ∙ ap (λ K → K ×ᴳ (C (pos O) (⊙Susp (n -⊙Torus))
                     ×ᴳ C (pos O) (n -⊙Torus)))
       (C-Sphere-diag 1)
  ∙ ap (λ K → C O (⊙Sphere O) ×ᴳ K)
       (ap2 _×ᴳ_
         (C-Susp O (n -⊙Torus) ∙ C-nTorus O n)
         (C-nTorus (pos O) n)
        ∙ ×ᴳ-unit-l {G = C O (⊙Sphere 0) ^ᴳ (n choose' pos O)})

C-nTorus (pos (S k)) O =
  C-Unit-is-trivial (pos (S k))

C-nTorus (pos (S k)) (S n) =
  C-Sphere× (pos (S k)) 1 (n -⊙Torus)
  ∙ ap (λ K → K ×ᴳ (C (pos (S k)) (⊙Susp (n -⊙Torus))
                     ×ᴳ C (pos (S k)) (n -⊙Torus)))
       (C-Sphere-≠ (pos (S k)) 1 (ℕ-S≠O k ∘ pos-injective (S k) 0))
  ∙ ×ᴳ-unit-l {G = (C (pos (S k)) (⊙Susp (n -⊙Torus))
                    ×ᴳ (C (pos (S k)) (n -⊙Torus)))}
  ∙ ap2 _×ᴳ_ (C-Susp (pos k) (n -⊙Torus) ∙ C-nTorus (pos k) n)
             (C-nTorus (pos (S k)) n)
  ∙ ^ᴳ-sum (C O (⊙Sphere 0)) (n choose' pos k) (n choose' pos (S k))
