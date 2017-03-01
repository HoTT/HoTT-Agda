{-# OPTIONS --without-K --rewriting #-}

open import HoTT

{-
                 K
                 ↑
                 ╎ ψ₁
            q[_] ╎    ψ₂
   Coker ψ₂ ↞--- G ←------ L
      ↑          ↑
   φ₁ ╎          ╎ inject
      ↑          ↑
      H ↞------- Ker ψ₁
           φ₂

     Then, H ≃ᴳ Ker/Im.
-}

module groups.KernelImageUniqueFactorization {i j k l}
  {G : Group i} {H : Group j} {K : Group k} {L : Group l}
  (ψ₁ : G →ᴳ K) (ψ₂ : L →ᴳ G) (G-ab : is-abelian G)
  (φ₁ : Ker ψ₁ →ᴳ H) (φ₁-is-surj : is-surjᴳ φ₁)
  (φ₂ : H →ᴳ Coker ψ₂ G-ab) (φ₂-is-inj : is-injᴳ φ₂)
  (φ-comm : ∀ ker → GroupHom.f (φ₂ ∘ᴳ φ₁) ker == q[ fst ker ])
  where

  private
    module G = Group G
    module H = Group H
    module K = Group K
    module L = Group L
    module ψ₁ = GroupHom ψ₁
    module ψ₂ = GroupHom ψ₂
    module φ₁ = GroupHom φ₁
    module φ₂ = GroupHom φ₂

  open import groups.PropQuotUniqueFactorization
    (ker-propᴳ ψ₁) (im-npropᴳ ψ₂ G-ab) φ₁ φ₁-is-surj φ₂ φ₂-is-inj φ-comm
  open import groups.KernelImage ψ₁ ψ₂ G-ab

  H-iso-Ker/Im : H ≃ᴳ Ker/Im
  H-iso-Ker/Im = Ker/Im-β ⁻¹ᴳ ∘eᴳ H-iso-P/Q
