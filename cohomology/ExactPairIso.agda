{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness

module cohomology.ExactPairIso where

{- An exact sequence 0 → G → H → 0 implies that G == H -}

module _ {i} {G H K L : Group i} {φ : GroupHom H K}
  (ex : ExactSeq (G ⟨ cst-hom ⟩→ H ⟨ φ ⟩→ K ⟨ cst-hom ⟩→ L ⊣|)) where

  private
    inj : (h₁ h₂ : Group.El H) → GroupHom.f φ h₁ == GroupHom.f φ h₂ → h₁ == h₂
    inj = zero-kernel-injective φ
      (λ h p → Trunc-rec (Group.El-level H _ _) (λ s → ! (snd s))
                 (ktoi (exact-get ex 0) h p))

  exact-pair-iso : H == K
  exact-pair-iso = surj-inj-iso φ inj (λ k → ktoi (exact-get ex 1) k idp)

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
