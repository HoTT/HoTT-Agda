{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness

module cohomology.ExactPairIso where

{- An exact sequence 0 → G → H → 0 implies that G == H -}

module _ {i} {G H : Group i} {φ : GroupHom G H}
  (ex : ExactSeq (0G ⟨ cst-hom ⟩→ G ⟨ φ ⟩→ H ⟨ cst-hom ⟩→ 0G ⊣|)) where

  private
    inj : (g₁ g₂ : Group.El G) → GroupHom.f φ g₁ == GroupHom.f φ g₂ → g₁ == g₂
    inj = zero-kernel-injective φ
      (λ g p → Trunc-rec (Group.El-level G _ _) (λ s → ! (snd s))
                 (ktoi (exact-get ex 0) g p))

  exact-pair-iso : G == H
  exact-pair-iso = surj-inj-iso φ inj (λ h → ktoi (exact-get ex 1) h idp)

module _ {i} {G H K J : Group i} {φ : GroupHom G H} {ψ : GroupHom H K}
  {χ : GroupHom K J} (p : G == 0G) (q : J == 0G)
  (ex : ExactSeq (G ⟨ φ ⟩→ H ⟨ ψ ⟩→ K ⟨ χ ⟩→ J ⊣|)) where

  private
    ex₁ : ExactSeq (0G ⟨ cst-hom ⟩→ H ⟨ ψ ⟩→ K ⟨ χ ⟩→ J ⊣|)
    ex₁ = transport
      (λ {(G' , φ') → ExactSeq (G' ⟨ φ' ⟩→ H ⟨ ψ ⟩→ K ⟨ χ ⟩→ J ⊣|)})
      (pair= p (prop-has-all-paths-↓ {B = λ L → GroupHom L H}
                 (raise-level ⟨-2⟩ 0G-hom-out-level)))
      ex

    ex₂ : ExactSeq (0G ⟨ cst-hom ⟩→ H ⟨ ψ ⟩→ K ⟨ cst-hom ⟩→ 0G ⊣|)
    ex₂ = transport
      (λ {(J' , χ') → ExactSeq (0G ⟨ cst-hom ⟩→ H ⟨ ψ ⟩→ K ⟨ χ' ⟩→ J' ⊣|)})
      (pair= q (prop-has-all-paths-↓ {B = λ L → GroupHom K L}
                 (raise-level _ 0G-hom-in-level)))
      ex₁

  exact-pair-path-iso : H == K
  exact-pair-path-iso = exact-pair-iso ex₂
