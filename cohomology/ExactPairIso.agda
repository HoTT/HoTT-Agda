{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness

module cohomology.ExactPairIso where

{- An exact sequence 0 → G → H → 0 implies that G == H -}

module _ {i} {G H : Group i} (φ : GroupHom G H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

  module _ (ex : ExactSeq (0G ⟨ cst-hom ⟩→ G ⟨ φ ⟩→ H ⟨ cst-hom ⟩→ 0G ⊣|))
    where

    private
      inj : (g₁ g₂ : G.El) → φ.f g₁ == φ.f g₂ → g₁ == g₂
      inj = zero-kernel-injective φ
        (λ g p → Trunc-rec (G.El-level _ _) (λ s → ! (snd s))
                   (fst (exact-get ex 0) g p))

    exact-pair-iso : G == H
    exact-pair-iso = surj-inj-iso φ inj (λ h → fst (exact-get ex 1) h idp)
