{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.Function2
open import lib.types.Group
open import lib.types.Sigma
open import lib.types.Truncation
open import lib.groups.Homomorphism
open import lib.groups.SubgroupProp

module lib.groups.Subgroup where

module _ {i j} {G : Group i} (P : SubgroupProp G j) where
  private
    module G = Group G
    module P = SubgroupProp P

  subgroup-struct : GroupStructure P.SubEl
  subgroup-struct = record {M} where
    module M where
      ident : P.SubEl
      ident = G.ident , P.ident

      inv : P.SubEl → P.SubEl
      inv (g , p) = G.inv g , P.inv p

      comp : P.SubEl → P.SubEl → P.SubEl
      comp (g₁ , p₁) (g₂ , p₂) = G.comp g₁ g₂ , P.comp p₁ p₂

      abstract
        unit-l : ∀ g → comp ident g == g
        unit-l (g , _) = Subtype=-out P.sub-El-prop (G.unit-l g)

        unit-r : ∀ g → comp g ident == g
        unit-r (g , _) = Subtype=-out P.sub-El-prop (G.unit-r g)

        assoc : ∀ g₁ g₂ g₃ → comp (comp g₁ g₂) g₃ == comp g₁ (comp g₂ g₃)
        assoc (g₁ , _) (g₂ , _) (g₃ , _) = Subtype=-out P.sub-El-prop (G.assoc g₁ g₂ g₃)

        inv-l : ∀ g → comp (inv g) g == ident
        inv-l (g , _) = Subtype=-out P.sub-El-prop (G.inv-l g)

        inv-r : ∀ g → comp g (inv g) == ident
        inv-r (g , _) = Subtype=-out P.sub-El-prop (G.inv-r g)

  Subgroup : Group (lmax i j)
  Subgroup = group _ (Subtype-level P.sub-El-prop G.El-level) subgroup-struct

module Subgroup {i j} {G : Group i} (P : SubgroupProp G j) where
  private
    module G = Group G
    module P = SubgroupProp P

  open Group (Subgroup P) public

  inject : Subgroup P →ᴳ G
  inject = record {
    f = λ {(g , _) → g};
    pres-comp = λ _ _ → idp}

  inject-lift : ∀ {j} {H : Group j} (φ : H →ᴳ G)
    → Π (Group.El H) (P.prop ∘ GroupHom.f φ)
    → (H →ᴳ Subgroup P)
  inject-lift {H = H} φ P-all = record {
    f = λ g → (φ.f g , P-all g);
    pres-comp = λ g₁ g₂ → Subtype=-out P.sub-El-prop (φ.pres-comp g₁ g₂)}
    where
      module H = Group H
      module φ = GroupHom φ

module _ {i} {j} {G : Group i} {H : Group j} (φ : G →ᴳ H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

  Ker : Group (lmax i j)
  Ker = Subgroup (ker-propᴳ φ)

  module Ker = Subgroup (ker-propᴳ φ)

  Im : Group (lmax i j)
  Im = Subgroup (im-propᴳ φ)

  module Im = Subgroup (im-propᴳ φ)

  im-lift : G →ᴳ Im
  im-lift = Im.inject-lift φ (λ g → [ g , idp ])

  im-lift-is-surj : is-surjᴳ im-lift
  im-lift-is-surj (_ , s) = Trunc-fmap
    (λ {(g , p) → (g , Subtype=-out (_ , λ _ → Trunc-level) p)}) s
