{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cohomology.Theory
open import homotopy.PushoutSplit
open import cw.CW

module cw.cohomology.WedgeOfCells {i} (OT : OrdinaryTheory i)
  {n} (⊙skel : ⊙Skeleton {i} (S n)) where

open OrdinaryTheory OT
open import cohomology.Bouquet OT
open import cw.WedgeOfCells (⊙Skeleton.skel ⊙skel)

module _ (m : ℤ) where
  CXₙ/Xₙ₋₁ : Group i
  CXₙ/Xₙ₋₁ = C m ⊙Xₙ/Xₙ₋₁

  CEl-Xₙ/Xₙ₋₁ : Type i
  CEl-Xₙ/Xₙ₋₁ = Group.El CXₙ/Xₙ₋₁

  abstract
    CXₙ/Xₙ₋₁-is-abelian : is-abelian CXₙ/Xₙ₋₁
    CXₙ/Xₙ₋₁-is-abelian = C-is-abelian m ⊙Xₙ/Xₙ₋₁

  CXₙ/Xₙ₋₁-abgroup : AbGroup i
  CXₙ/Xₙ₋₁-abgroup = CXₙ/Xₙ₋₁ , CXₙ/Xₙ₋₁-is-abelian

CXₙ/Xₙ₋₁-diag-β : ⊙has-cells-with-choice 0 ⊙skel i
  → CXₙ/Xₙ₋₁ (ℕ-to-ℤ (S n)) ≃ᴳ Πᴳ (⊙cells-last ⊙skel) (λ _ → C2 0)
CXₙ/Xₙ₋₁-diag-β ac = C-Bouquet-diag (S n) (⊙cells-last ⊙skel) (⊙cells-last-has-choice ⊙skel ac)
                 ∘eᴳ C-emap (ℕ-to-ℤ (S n)) Bouquet-⊙equiv-Xₙ/Xₙ₋₁

abstract
  CXₙ/Xₙ₋₁-≠-is-trivial : ∀ {m} (m≠Sn : m ≠ ℕ-to-ℤ (S n))
    → ⊙has-cells-with-choice 0 ⊙skel i
    → is-trivialᴳ (CXₙ/Xₙ₋₁ m)
  CXₙ/Xₙ₋₁-≠-is-trivial {m} m≠Sn ac =
    iso-preserves'-trivial (C-emap m Bouquet-⊙equiv-Xₙ/Xₙ₋₁) $
      C-Bouquet-≠-is-trivial m (⊙cells-last ⊙skel) (S n) m≠Sn (⊙cells-last-has-choice ⊙skel ac)

  CXₙ/Xₙ₋₁-<-is-trivial : ∀ {m} (m<Sn : m < S n)
    → ⊙has-cells-with-choice 0 ⊙skel i
    → is-trivialᴳ (CXₙ/Xₙ₋₁ (ℕ-to-ℤ m))
  CXₙ/Xₙ₋₁-<-is-trivial m<Sn = CXₙ/Xₙ₋₁-≠-is-trivial (ℕ-to-ℤ-≠ (<-to-≠ m<Sn))

  CXₙ/Xₙ₋₁->-is-trivial : ∀ {m} (m>Sn : S n < m)
    → ⊙has-cells-with-choice 0 ⊙skel i
    → is-trivialᴳ (CXₙ/Xₙ₋₁ (ℕ-to-ℤ m))
  CXₙ/Xₙ₋₁->-is-trivial m>Sn = CXₙ/Xₙ₋₁-≠-is-trivial (≠-inv (ℕ-to-ℤ-≠ (<-to-≠ m>Sn)))
