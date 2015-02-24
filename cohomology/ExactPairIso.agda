{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness

module cohomology.ExactPairIso where

{- An exact sequence 0 → G → H → 0 implies that G == H -}

module _ {i} {G H K L : Group i} {φ : H →ᴳ K}
  (ex : is-exact-seq (G ⟨ cst-hom ⟩→ H ⟨ φ ⟩→ K ⟨ cst-hom ⟩→ L ⊣|)) where

  private
    inj : (h₁ h₂ : Group.El H) → GroupHom.f φ h₁ == GroupHom.f φ h₂ → h₁ == h₂
    inj = zero-kernel-injective φ
      (λ h p → Trunc-rec (Group.El-level H _ _) (λ s → ! (snd s))
                 (ktoi (exact-get ex 0) h p))

  exact-pair-iso : H == K
  exact-pair-iso = surj-inj-= φ inj (λ k → ktoi (exact-get ex 1) k idp)

module _ {i} {G H K J : Group i} {φ : G →ᴳ H} {ψ : H →ᴳ K}
  {χ : K →ᴳ J} (p : G == 0ᴳ) (q : J == 0ᴳ)
  (ex : is-exact-seq (G ⟨ φ ⟩→ H ⟨ ψ ⟩→ K ⟨ χ ⟩→ J ⊣|)) where

  private
    ex₁ : is-exact-seq (0ᴳ ⟨ cst-hom ⟩→ H ⟨ ψ ⟩→ K ⟨ χ ⟩→ J ⊣|)
    ex₁ = transport
      (λ {(G' , φ') → is-exact-seq (G' ⟨ φ' ⟩→ H ⟨ ψ ⟩→ K ⟨ χ ⟩→ J ⊣|)})
      (pair= p (prop-has-all-paths-↓ {B = λ L → L →ᴳ H}
                 (raise-level ⟨-2⟩ 0ᴳ-hom-out-level)))
      ex

    ex₂ : is-exact-seq (0ᴳ ⟨ cst-hom ⟩→ H ⟨ ψ ⟩→ K ⟨ cst-hom ⟩→ 0ᴳ ⊣|)
    ex₂ = transport
      (λ {(J' , χ') → is-exact-seq (0ᴳ ⟨ cst-hom ⟩→ H ⟨ ψ ⟩→ K ⟨ χ' ⟩→ J' ⊣|)})
      (pair= q (prop-has-all-paths-↓ {B = λ L → K →ᴳ L}
                 (raise-level _ 0ᴳ-hom-in-level)))
      ex₁

  exact-pair-path-iso : H == K
  exact-pair-path-iso = exact-pair-iso ex₂
