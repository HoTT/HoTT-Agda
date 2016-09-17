{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
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

  subgroup-struct : GroupStructure (Σ G.El P.prop)
  subgroup-struct = record {
    ident = (G.ident , P.ident);
    inv = λ {(g , p) → (G.inv g , P.inv p)};
    comp = λ {(g₁ , p₁) (g₂ , p₂) → (G.comp g₁ g₂ , P.comp p₁ p₂)};
    unit-l = λ {(g , _) → Subtype=-out (P.level _) (G.unit-l g)};
    unit-r = λ {(g , _) → Subtype=-out (P.level _) (G.unit-r g)};
    assoc = λ {(g₁ , _) (g₂ , _) (g₃ , _) → Subtype=-out (P.level _) (G.assoc g₁ g₂ g₃)};
    inv-l = λ {(g , _) → Subtype=-out (P.level _) (G.inv-l g)};
    inv-r = λ {(g , _) → Subtype=-out (P.level _) (G.inv-r g)}}

  Subgroup : Group (lmax i j)
  Subgroup = group _ (Subtype-level G.El-level P.level) subgroup-struct

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
    pres-comp = λ g₁ g₂ → Subtype=-out (P.level _) (φ.pres-comp g₁ g₂)}
    where
      module H = Group H
      module φ = GroupHom φ

module _ {i} {j} {G : Group i} {H : Group j} (φ : G →ᴳ H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

  Ker : Group (lmax i j)
  Ker = Subgroup (ker-subgroup-prop φ)

  module Ker = Subgroup (ker-subgroup-prop φ)

  Im : Group (lmax i j)
  Im = Subgroup (im-subgroup-prop φ)

  module Im = Subgroup (im-subgroup-prop φ)

  im-lift : G →ᴳ Im
  im-lift = Im.inject-lift φ (λ g → [ g , idp ])

  im-lift-surj : (h : Group.El Im) → Trunc -1 (hfiber (GroupHom.f im-lift) h)
  im-lift-surj (_ , s) = Trunc-fmap (λ {(g , p) → (g , Subtype=-out Trunc-level p)}) s
