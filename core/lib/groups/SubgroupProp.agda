{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Group
open import lib.types.Sigma
open import lib.types.Truncation
open import lib.groups.Homomorphism

module lib.groups.SubgroupProp where

record SubgroupProp {i} (G : Group i) j : Type (lmax i (lsucc j)) where
  private
    module G = Group G
  field
    prop : Group.El G → Type j
    level : ∀ g → is-prop (prop g)
    ident : prop G.ident
    comp-inv-r : ∀ {g₁ g₂} → prop g₁ → prop g₂ → prop (G.comp g₁ (G.inv g₂))

  abstract
    inv : ∀ {g} → prop g → prop (G.inv g)
    inv pg = transport prop (G.unit-l _) (comp-inv-r ident pg)

    comp : ∀ {g₁ g₂} → prop g₁ → prop g₂ → prop (G.comp g₁ g₂)
    comp {g₁} {g₂} pg₁ pg₂ =
      transport prop (ap (G.comp g₁) (G.inv-inv g₂)) (comp-inv-r pg₁ (inv pg₂))
    
module _ {i} {j} {G : Group i} {H : Group j} (φ : G →ᴳ H) where
  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

  ker-subgroup-prop : SubgroupProp G j
  ker-subgroup-prop = record {
    prop = λ g → φ.f g == H.ident;
    level = λ g → H.El-level _ _;
    ident = φ.pres-ident;
    comp-inv-r = λ p₁ p₂
      → φ.pres-comp _ _
      ∙ ap2 H.comp p₁ (φ.pres-inv _ ∙ ap H.inv p₂ ∙ H.inv-ident)
      ∙ H.unit-l _ }

  im-subgroup-prop : SubgroupProp H (lmax i j)
  im-subgroup-prop = record {
    prop = λ h → Trunc -1 (hfiber φ.f h);
    level = λ h → Trunc-level;
    ident = [ G.ident , φ.pres-ident ];
    comp-inv-r = Trunc-fmap2 (λ {(g₁ , p₁) (g₂ , p₂)
      → G.comp g₁ (G.inv g₂)
      , φ.pres-comp g₁ (G.inv g₂)
      ∙ ap2 H.comp p₁ (φ.pres-inv g₂ ∙ ap H.inv p₂)})}

is-closed-under-congruence : ∀ {i j} {G : Group i} → SubgroupProp G j → Type (lmax i j)
is-closed-under-congruence {G = G} P =
  ∀ g₁ {g₂} → SubgroupProp.prop P g₂ → SubgroupProp.prop P (Group.cong G g₁ g₂)

NormalSubgroupProp : ∀ {i} (G : Group i) j → Type (lmax i (lsucc j))
NormalSubgroupProp {i} G j = Σ (SubgroupProp G j) is-closed-under-congruence

module NormalSubgroupProp {i j} {G : Group i} (normal-prop : NormalSubgroupProp G j) where
  private
    module G = Group G

  subgrp-prop : SubgroupProp G j
  subgrp-prop = fst normal-prop
  open SubgroupProp subgrp-prop public

  cong : ∀ g₁ {g₂} → prop g₂ → prop (G.cong g₁ g₂)
  cong = snd normal-prop

  abstract
    comm : ∀ g₁ g₂ → prop (G.comp g₁ g₂) → prop (G.comp g₂ g₁)
    comm g₁ g₂ pg₁g₂ = transport prop
      ( ap (λ g → G.comp g (G.inv g₂)) (! (G.assoc g₂ g₁ g₂))
      ∙ G.assoc (G.comp g₂ g₁) g₂ (G.inv g₂)
      ∙ ap (G.comp (G.comp g₂ g₁)) (G.inv-r g₂)
      ∙ G.unit-r (G.comp g₂ g₁))
      (cong g₂ pg₁g₂)
    {- So far this is not used.
    uncong : ∀ g₁ g₂ → prop (G.cong g₁ g₂) → prop g₂
    uncong g₁ g₂ pg₁g₂ = transport prop path (cong (G.inv g₁) pg₁g₂) where
      path : G.cong (G.inv g₁) (G.cong g₁ g₂) == g₂
      path = ! (G.cong-comp-l (G.inv g₁) g₁ g₂) ∙ ap (λ g → G.cong g g₂) (G.inv-l g₁) ∙ G.cong-unit-l g₂
    -}

abelian-subgroup-prop-is-normal : ∀ {i j} {G : Group i} (P : SubgroupProp G j)
  → (∀ g₁ g₂ → SubgroupProp.prop P (Group.comp G g₁ g₂)
             → SubgroupProp.prop P (Group.comp G g₂ g₁))
  → is-closed-under-congruence P
abelian-subgroup-prop-is-normal {G = G} P P-comm g₁ {g₂} Pg₂ =
  transport! P.prop (G.assoc g₁ g₂ (G.inv g₁)) $
    P-comm (G.comp g₂ (G.inv g₁)) g₁ $
      transport! P.prop
        ( G.assoc g₂ (G.inv g₁) g₁
        ∙ ap (G.comp g₂) (G.inv-l g₁)
        ∙ G.unit-r g₂)
        Pg₂
  where module G = Group G
        module P = SubgroupProp P

abelian-subgroup-prop-normal : ∀ {i j} {G : Group i} (P : SubgroupProp G j)
  → (∀ g₁ g₂ → SubgroupProp.prop P (Group.comp G g₁ g₂) → SubgroupProp.prop P (Group.comp G g₂ g₁))
  → NormalSubgroupProp G j
abelian-subgroup-prop-normal P P-comm = P , abelian-subgroup-prop-is-normal P P-comm

sub-abelian-group-prop-is-normal : ∀ {i j} {G : Group i}
  → (G-is-abelian : is-abelian G)
  → (P : SubgroupProp G j)
  → is-closed-under-congruence P
sub-abelian-group-prop-is-normal {G = G} G-is-abelian P =
  abelian-subgroup-prop-is-normal P λ g₁ g₂ Pg₁g₂ → transport P.prop (G.comm g₁ g₂) Pg₁g₂
  where module G = AbelianGroup (G , G-is-abelian)
        module P = SubgroupProp P

is-closed-under-comp-with : ∀ {i j k} {G : Group i}
  → SubgroupProp G j → SubgroupProp G k → Type (lmax i (lmax j k))
is-closed-under-comp-with {G = G} P Q =
  ∀ {g₁ g₂} → P.prop g₁ → Q.prop g₂ → P.prop (Group.comp G g₁ g₂)
  where module P = SubgroupProp P
        module Q = SubgroupProp Q

is-subsubgroup-prop : ∀ {i j k} {G : Group i}
  → SubgroupProp G j → SubgroupProp G k → Type (lmax i (lmax j k))
is-subsubgroup-prop P Q = ∀ g → P.prop g → Q.prop g
  where module P = SubgroupProp P
        module Q = SubgroupProp Q
