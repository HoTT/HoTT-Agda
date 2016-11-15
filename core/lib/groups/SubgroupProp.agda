{-# OPTIONS --without-K --rewriting #-}

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
    -- In theory being inhabited implies that the identity is included,
    -- but in practice let's just prove the identity case.
    ident : prop G.ident
    diff : ∀ {g₁ g₂} → prop g₁ → prop g₂ → prop (G.diff g₁ g₂)

  subEl-prop : SubtypeProp G.El j
  subEl-prop = prop , level
  SubEl = Subtype subEl-prop

  abstract
    {-
      ident : prop G.ident
      ident = transport prop (G.inv-r (fst inhab)) (diff (snd inhab) (snd inhab))
    -}

    inv : ∀ {g} → prop g → prop (G.inv g)
    inv pg = transport prop (G.unit-l _) (diff ident pg)

    comp : ∀ {g₁ g₂} → prop g₁ → prop g₂ → prop (G.comp g₁ g₂)
    comp {g₁} {g₂} pg₁ pg₂ =
      transport prop (ap (G.comp g₁) (G.inv-inv g₂)) (diff pg₁ (inv pg₂))

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

  propᴳ : SubgroupProp G j
  propᴳ = fst normal-prop
  open SubgroupProp propᴳ public

  conj : is-normal propᴳ
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
  comm-is-normal : ∀ {i j} {G : Group i} (P : SubgroupProp G j)
    → (∀ g₁ g₂ → SubgroupProp.prop P (Group.comp G g₁ g₂)
               → SubgroupProp.prop P (Group.comp G g₂ g₁))
    → is-normal P
  comm-is-normal {G = G} P P-comm g₁ {g₂} Pg₂ =
    transport! P.prop (G.assoc g₁ g₂ (G.inv g₁)) $
      P-comm (G.diff g₂ g₁) g₁ $
        transport! P.prop
          ( G.assoc g₂ (G.inv g₁) g₁
          ∙ ap (G.comp g₂) (G.inv-l g₁)
          ∙ G.unit-r g₂)
          Pg₂
    where module G = Group G
          module P = SubgroupProp P

  sub-abelian-is-normal : ∀ {i j} {G : Group i}
    → (G-is-abelian : is-abelian G)
    → (P : SubgroupProp G j)
    → is-normal P
  sub-abelian-is-normal {G = G} G-is-abelian P =
    comm-is-normal P λ g₁ g₂ Pg₁g₂ → transport P.prop (G.comm g₁ g₂) Pg₁g₂
    where module G = AbGroup (G , G-is-abelian)
          module P = SubgroupProp P

sub-abelian-normal : ∀ {i j} {G : Group i}
  → (G-is-abelian : is-abelian G)
  → SubgroupProp G j
  → NormalSubgroupProp G j
sub-abelian-normal G-is-abelian P = P , sub-abelian-is-normal G-is-abelian P

{- Subgroups of subgroups -}

infix 40 _⊆ᴳ_
_⊆ᴳ_ : ∀ {i j k} {G : Group i}
  → SubgroupProp G j → SubgroupProp G k → Type (lmax i (lmax j k))
P ⊆ᴳ Q = ∀ g → P.prop g → Q.prop g
  where module P = SubgroupProp P
        module Q = SubgroupProp Q

{- triviality -}

trivial-propᴳ : ∀ {i} (G : Group i) → SubgroupProp G i
trivial-propᴳ {i} G = record {M} where
  module G = Group G
  module M where
    prop : G.El → Type i
    prop g = g == G.ident

    ident : prop G.ident
    ident = idp

    level : ∀ g → is-prop (prop g)
    level g = G.El-level g G.ident

    abstract
      diff : {g₁ g₂ : G.El} → prop g₁ → prop g₂ → prop (G.diff g₁ g₂)
      diff g₁=id g₂=id = ap2 G.comp g₁=id (ap G.inv g₂=id ∙ G.inv-ident)
                       ∙ G.unit-r G.ident

is-trivial-propᴳ : ∀ {i j} {G : Group i} → SubgroupProp G j → Type (lmax i j)
is-trivial-propᴳ {G = G} P = P ⊆ᴳ trivial-propᴳ G
