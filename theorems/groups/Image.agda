{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module groups.Image where

module _ {i j k} {G : Group i} {H : Group j}
  {K : Group k} (φ : H →ᴳ K) (ψ : G →ᴳ H) where

  abstract
    im-sub-im-∘ : is-surjᴳ ψ → im-propᴳ φ ⊆ᴳ im-propᴳ (φ ∘ᴳ ψ)
    im-sub-im-∘ ψ-is-surj k = Trunc-rec Trunc-level
      (λ{(h , φh=k) → Trunc-rec Trunc-level
        (λ{(g , ψg=h) → [ g , ap (GroupHom.f φ) ψg=h ∙ φh=k ]})
        (ψ-is-surj h)})

    im-∘-sub-im : im-propᴳ (φ ∘ᴳ ψ) ⊆ᴳ im-propᴳ φ
    im-∘-sub-im k = Trunc-rec Trunc-level
      (λ{(g , φψg=k) → [ GroupHom.f ψ g , φψg=k ]})

  im-iso-im-pre∘ : is-surjᴳ ψ → Im φ ≃ᴳ Im (φ ∘ᴳ ψ)
  im-iso-im-pre∘ ψ-is-surj = Subgroup-emap-r
    (im-propᴳ φ) (im-propᴳ (φ ∘ᴳ ψ))
    (im-sub-im-∘ ψ-is-surj) im-∘-sub-im
