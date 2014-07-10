{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.Equivalences2
open import lib.NType2
open import lib.types.Group

module lib.groups.Homomorphisms where

{- constant homomorphism -}
module _ where
  cst-hom : ∀ {i j} {G : Group i} {H : Group j} → GroupHom G H
  cst-hom {H = H} = group-hom (cst ident) idp (λ _ _ → ! (unitl _))
    where open Group H

  pre∘-cst-hom : ∀ {i j k} {G : Group i} {H : Group j} {K : Group k}
    (φ : GroupHom H K)
    → φ ∘hom cst-hom {G = G} {H = H} == cst-hom
  pre∘-cst-hom φ = hom= _ _ (λ= (λ g → GroupHom.pres-ident φ))

{- homomorphism with kernel zero is injective -}
module _ {i j} {G : Group i} {H : Group j} (φ : GroupHom G H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

  zero-kernel-injective : ((g : G.El) → φ.f g == H.ident → g == G.ident)
    → ((g₁ g₂ : G.El) → φ.f g₁ == φ.f g₂ → g₁ == g₂)
  zero-kernel-injective f g₁ g₂ p =
    ! (inv-inv G g₁) ∙ group-inv-unique-r G (G.inv g₁) g₂ (f _ $
      φ.f (G.comp (G.inv g₁) g₂)
        =⟨ φ.pres-comp (G.inv g₁) g₂ ⟩
      H.comp (φ.f (G.inv g₁)) (φ.f g₂)
        =⟨ grouphom-pres-inv φ g₁ |in-ctx (λ w → H.comp w (φ.f g₂)) ⟩
      H.comp (H.inv (φ.f g₁)) (φ.f g₂)
        =⟨ p |in-ctx (λ w → H.comp (H.inv w) (φ.f g₂)) ⟩
      H.comp (H.inv (φ.f g₂)) (φ.f g₂)
        =⟨ H.invl (φ.f g₂) ⟩
      H.ident ∎)

{- a surjective and injective homomorphism is an isomorphism -}
module _ {i j} {G : Group i} {H : Group j} (φ : GroupHom G H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

  module _ (inj : (g₁ g₂ : G.El) → φ.f g₁ == φ.f g₂ → g₁ == g₂)
    (surj : (h : H.El) → Σ G.El (λ g → φ.f g == h)) where

    surj-inj-equiv : is-equiv φ.f
    surj-inj-equiv = contr-map-is-equiv
      (λ h → let (g₁ , p₁) = surj h in
        ((g₁ , p₁) , (λ {(g₂ , p₂) →
          pair= (inj g₁ g₂ (p₁ ∙ ! p₂))
                (prop-has-all-paths-↓ (H.El-level _ _))})))

module _ {i} {G H : Group i} (φ : GroupHom G H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

  module _ (inj : (g₁ g₂ : G.El) → φ.f g₁ == φ.f g₂ → g₁ == g₂)
    (surj : (h : H.El) → Σ G.El (λ g → φ.f g == h)) where

    surj-inj-iso : G == H
    surj-inj-iso = group-iso φ (surj-inj-equiv φ inj surj)
