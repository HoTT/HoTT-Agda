{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Group
open import lib.types.Sigma
open import lib.types.Truncation

module lib.groups.SubgroupProp where

record SubgroupProp {i} (G : Group i) j : Type (lmax i (lsucc j)) where
  private
    module G = Group G
  field
    prop : G.El → Type j
    level : ∀ g → is-prop (prop g)
  sub-El-prop : SubtypeProp G.El j
  sub-El-prop = prop , level
  SubEl = Subtype sub-El-prop
  field
    inhab : SubEl
    comp-inv-r : ∀ {g₁ g₂} → prop g₁ → prop g₂ → prop (G.comp g₁ (G.inv g₂))

  abstract
    ident : prop G.ident
    ident = transport prop (G.inv-r (fst inhab)) (comp-inv-r (snd inhab) (snd inhab))

    inv : ∀ {g} → prop g → prop (G.inv g)
    inv pg = transport prop (G.unit-l _) (comp-inv-r ident pg)

    comp : ∀ {g₁ g₂} → prop g₁ → prop g₂ → prop (G.comp g₁ g₂)
    comp {g₁} {g₂} pg₁ pg₂ =
      transport prop (ap (G.comp g₁) (G.inv-inv g₂)) (comp-inv-r pg₁ (inv pg₂))

trivial-propᴳ : ∀ {i} (G : Group i) → SubgroupProp G i
trivial-propᴳ G = record {
  prop = λ g → g == G.ident;
  level = λ g → G.El-level g G.ident;
  inhab = G.ident , idp;
  comp-inv-r = λ g₁=id g₂=id
    → ap2 G.comp g₁=id (ap G.inv g₂=id ∙ G.inv-ident)
    ∙ G.unit-r G.ident}
  where module G = Group G

is-fullᴳ : ∀ {i j} {G : Group i} → SubgroupProp G j → Type (lmax i j)
is-fullᴳ P = ∀ g → SubgroupProp.prop P g

-- Normal subgroups

is-normal : ∀ {i j} {G : Group i} → SubgroupProp G j → Type (lmax i j)
is-normal {G = G} P = ∀ g₁ {g₂} → P.prop g₂ → P.prop (Group.conj G g₁ g₂)
  where module P = SubgroupProp P

NormalSubgroupProp : ∀ {i} (G : Group i) j → Type (lmax i (lsucc j))
NormalSubgroupProp {i} G j = Σ (SubgroupProp G j) is-normal

module NormalSubgroupProp {i j} {G : Group i} (normal-prop : NormalSubgroupProp G j) where
  private
    module G = Group G

  subgrp-prop : SubgroupProp G j
  subgrp-prop = fst normal-prop
  open SubgroupProp subgrp-prop public

  conj : is-normal subgrp-prop
  conj = snd normal-prop

  abstract
    comm : ∀ g₁ g₂ → prop (G.comp g₁ g₂) → prop (G.comp g₂ g₁)
    comm g₁ g₂ pg₁g₂ = transport prop
      ( ap (λ g → G.comp g (G.inv g₂)) (! (G.assoc g₂ g₁ g₂))
      ∙ G.assoc (G.comp g₂ g₁) g₂ (G.inv g₂)
      ∙ ap (G.comp (G.comp g₂ g₁)) (G.inv-r g₂)
      ∙ G.unit-r (G.comp g₂ g₁))
      (conj g₂ pg₁g₂)
    {- So far this is not used.
    unconj : ∀ g₁ g₂ → prop (G.conj g₁ g₂) → prop g₂
    unconj g₁ g₂ pg₁g₂ = transport prop path (conj (G.inv g₁) pg₁g₂) where
      path : G.conj (G.inv g₁) (G.conj g₁ g₂) == g₂
      path = ! (G.conj-comp-l (G.inv g₁) g₁ g₂) ∙ ap (λ g → G.conj g g₂) (G.inv-l g₁) ∙ G.conj-unit-l g₂
    -}

abstract
  abelian-subgroup-is-normal : ∀ {i j} {G : Group i} (P : SubgroupProp G j)
    → (∀ g₁ g₂ → SubgroupProp.prop P (Group.comp G g₁ g₂)
               → SubgroupProp.prop P (Group.comp G g₂ g₁))
    → is-normal P
  abelian-subgroup-is-normal {G = G} P P-comm g₁ {g₂} Pg₂ =
    transport! P.prop (G.assoc g₁ g₂ (G.inv g₁)) $
      P-comm (G.comp g₂ (G.inv g₁)) g₁ $
        transport! P.prop
          ( G.assoc g₂ (G.inv g₁) g₁
          ∙ ap (G.comp g₂) (G.inv-l g₁)
          ∙ G.unit-r g₂)
          Pg₂
    where module G = Group G
          module P = SubgroupProp P

abelian-subgroup-normal : ∀ {i j} {G : Group i} (P : SubgroupProp G j)
  → (∀ g₁ g₂ → SubgroupProp.prop P (Group.comp G g₁ g₂) → SubgroupProp.prop P (Group.comp G g₂ g₁))
  → NormalSubgroupProp G j
abelian-subgroup-normal P P-comm = P , abelian-subgroup-is-normal P P-comm

abstract
  sub-abelian-group-is-normal : ∀ {i j} {G : Group i}
    → (G-is-abelian : is-abelian G)
    → (P : SubgroupProp G j)
    → is-normal P
  sub-abelian-group-is-normal {G = G} G-is-abelian P =
    abelian-subgroup-is-normal P λ g₁ g₂ Pg₁g₂ → transport P.prop (G.comm g₁ g₂) Pg₁g₂
    where module G = AbelianGroup (G , G-is-abelian)
          module P = SubgroupProp P

is-closed-under-comp-with : ∀ {i j k} {G : Group i}
  → SubgroupProp G j → SubgroupProp G k → Type (lmax i (lmax j k))
is-closed-under-comp-with {G = G} P Q =
  ∀ {g₁ g₂} → P.prop g₁ → Q.prop g₂ → P.prop (Group.comp G g₁ g₂)
  where module P = SubgroupProp P
        module Q = SubgroupProp Q

{- Subgroups of subgroups -}

infix 40 _⊆ᴳ_
_⊆ᴳ_ : ∀ {i j k} {G : Group i}
  → SubgroupProp G j → SubgroupProp G k → Type (lmax i (lmax j k))
P ⊆ᴳ Q = ∀ g → P.prop g → Q.prop g
  where module P = SubgroupProp P
        module Q = SubgroupProp Q
