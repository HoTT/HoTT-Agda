{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.Function2
open import lib.types.Group
open import lib.types.Sigma
open import lib.types.Truncation
open import lib.groups.Homomorphism
open import lib.groups.Isomorphism
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
        unit-l (g , _) = Subtype=-out P.subEl-prop (G.unit-l g)

        unit-r : ∀ g → comp g ident == g
        unit-r (g , _) = Subtype=-out P.subEl-prop (G.unit-r g)

        assoc : ∀ g₁ g₂ g₃ → comp (comp g₁ g₂) g₃ == comp g₁ (comp g₂ g₃)
        assoc (g₁ , _) (g₂ , _) (g₃ , _) = Subtype=-out P.subEl-prop (G.assoc g₁ g₂ g₃)

        inv-l : ∀ g → comp (inv g) g == ident
        inv-l (g , _) = Subtype=-out P.subEl-prop (G.inv-l g)

        inv-r : ∀ g → comp g (inv g) == ident
        inv-r (g , _) = Subtype=-out P.subEl-prop (G.inv-r g)

  Subgroup : Group (lmax i j)
  Subgroup = group _ (Subtype-level P.subEl-prop G.El-level) subgroup-struct

module Subgroup {i j} {G : Group i} (P : SubgroupProp G j) where
  private
    module G = Group G

  propᴳ = P
  module P = SubgroupProp propᴳ
  open P public using (prop; subEl-prop)

  grp = Subgroup P
  open Group grp public

  inject : Subgroup P →ᴳ G
  inject = record {f = fst; pres-comp = λ _ _ → idp}

  inject-lift : ∀ {j} {H : Group j} (φ : H →ᴳ G)
    → Π (Group.El H) (prop ∘ GroupHom.f φ)
    → (H →ᴳ Subgroup P)
  inject-lift {H = H} φ P-all = record {M} where
    module H = Group H
    module φ = GroupHom φ
    module M where
      f : H.El → Σ G.El prop
      f h = φ.f h , P-all h

      abstract
        pres-comp : ∀ h₁ h₂ → f (H.comp h₁ h₂) == Group.comp (Subgroup P) (f h₁) (f h₂)
        pres-comp h₁ h₂ = Subtype=-out subEl-prop (φ.pres-comp h₁ h₂)

module _ {i} {j} {G : Group i} {H : Group j} (φ : G →ᴳ H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

  module Ker = Subgroup (ker-propᴳ φ)
  Ker = Ker.grp

  module Im = Subgroup (im-propᴳ φ)
  Im = Im.grp

  im-lift : G →ᴳ Im
  im-lift = Im.inject-lift φ (λ g → [ g , idp ])

  im-lift-is-surj : is-surjᴳ im-lift
  im-lift-is-surj (_ , s) = Trunc-fmap
    (λ {(g , p) → (g , Subtype=-out (_ , λ _ → Trunc-level) p)}) s

module _ {i j k} {G : Group i} (P : SubgroupProp G j)
  (Q : SubgroupProp G k) where

  -- FIXME looks like a bad name
  Subgroup-fmap-r : P ⊆ᴳ Q → Subgroup P →ᴳ Subgroup Q
  Subgroup-fmap-r P⊆Q = group-hom (Σ-fmap-r P⊆Q)
    (λ _ _ → Subtype=-out (SubgroupProp.subEl-prop Q) idp)

  Subgroup-emap-r : P ⊆ᴳ Q → Q ⊆ᴳ P → Subgroup P ≃ᴳ Subgroup Q
  Subgroup-emap-r P⊆Q Q⊆P = Subgroup-fmap-r P⊆Q ,
    is-eq _ (Σ-fmap-r Q⊆P)
      (λ _ → Subtype=-out (SubgroupProp.subEl-prop Q) idp)
      (λ _ → Subtype=-out (SubgroupProp.subEl-prop P) idp)
