{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Group
open import lib.types.Sigma
open import lib.types.Truncation
open import lib.groups.Homomorphisms

module lib.groups.PropSubgroup where

record induces-subgroup {i j} (G : Group i) (P : Group.El G → Type j)
  : Type (lmax i j) where
  private
    module G = Group G
  field
    level : ∀ g → is-prop (P g)
    ident : P G.ident
    comp-inv-r : ∀ {g₁ g₂} → P g₁ → P g₂ → P (G.comp g₁ (G.inv g₂))

  abstract
    inv : ∀ {g} → P g → P (G.inv g)
    inv pg = transport P (G.unit-l _) (comp-inv-r ident pg)

    comp : ∀ {g₁ g₂} → P g₁ → P g₂ → P (G.comp g₁ g₂)
    comp {g₁} {g₂} pg₁ pg₂ =
      transport P (ap (G.comp g₁) (G.inv-inv g₂)) (comp-inv-r pg₁ (inv pg₂))

module PropSubgroup {i j} {G : Group i} {P : Group.El G → Type j}
  (P-induces-subgroup : induces-subgroup G P) where
  private
    module G = Group G
    module P = induces-subgroup P-induces-subgroup

  struct : GroupStructure (Σ G.El P)
  struct = record {
    ident = (G.ident , P.ident);
    inv = λ {(g , p) → (G.inv g , P.inv p)};
    comp = λ {(g₁ , p₁) (g₂ , p₂) → (G.comp g₁ g₂ , P.comp p₁ p₂)};
    unit-l = λ {(g , _) → Subtype=-out (P.level _) (G.unit-l g)};
    unit-r = λ {(g , _) → Subtype=-out (P.level _) (G.unit-r g)};
    assoc = λ {(g₁ , _) (g₂ , _) (g₃ , _) → Subtype=-out (P.level _) (G.assoc g₁ g₂ g₃)};
    inv-l = λ {(g , _) → Subtype=-out (P.level _) (G.inv-l g)};
    inv-r = λ {(g , _) → Subtype=-out (P.level _) (G.inv-r g)}}

  Subgroup : Group (lmax i j)
  Subgroup = group _ (Subtype-level G.El-level P.level) struct

  inj : Subgroup →ᴳ G
  inj = record {
    f = λ {(g , _) → g};
    pres-comp = λ _ _ → idp}

  prop-hom : ∀ {j} {H : Group j} (φ : H →ᴳ G)
    → Π (Group.El H) (P ∘ GroupHom.f φ) → (H →ᴳ Subgroup)
  prop-hom {H = H} φ p = record {
    f = λ g → (φ.f g , p g);
    pres-comp = λ g₁ g₂ → Subtype=-out (P.level _) (φ.pres-comp g₁ g₂)}
    where
      module H = Group H
      module φ = GroupHom φ

module _ {i} {j} {G : Group i} {H : Group j} (φ : G →ᴳ H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

    ker-induces-subgroup : induces-subgroup G (λ g → φ.f g == H.ident)
    ker-induces-subgroup = record {
      level = (λ g → H.El-level _ _);
      ident = φ.pres-ident;
      comp-inv-r = λ p₁ p₂
        → φ.pres-comp _ _
        ∙ ap2 H.comp p₁ (φ.pres-inv _ ∙ ap H.inv p₂ ∙ H.inv-ident)
        ∙ H.unit-l _ }

    im-induces-subgroup : induces-subgroup H (λ h → Trunc -1 (hfiber φ.f h))
    im-induces-subgroup = record {
      level = λ h → Trunc-level;
      ident = [ G.ident , φ.pres-ident ];
      comp-inv-r = Trunc-fmap2 (λ {(g₁ , p₁) (g₂ , p₂)
        → G.comp g₁ (G.inv g₂)
        , φ.pres-comp g₁ (G.inv g₂)
        ∙ ap2 H.comp p₁ (φ.pres-inv g₂ ∙ ap H.inv p₂)})}

    module Ker = PropSubgroup ker-induces-subgroup

    module Im = PropSubgroup im-induces-subgroup

  open Ker public renaming
    (struct to ker-struct; Subgroup to Ker;
     inj to ker-inj; prop-hom to ker-hom)

  open Im public renaming
    (struct to im-struct; Subgroup to Im;
     inj to im-inj; prop-hom to im-out-hom)

  -- XXX Naming conventions.
  im-in-hom : G →ᴳ Im
  im-in-hom = record {
    f = λ g → (φ.f g , [ g , idp ]);
    pres-comp = λ g₁ g₂ → Subtype=-out Trunc-level (φ.pres-comp g₁ g₂)}

  im-in-surj : (h : Group.El Im) → Trunc -1 (hfiber (GroupHom.f im-in-hom) h)
  im-in-surj (_ , s) = Trunc-fmap (λ {(g , p) → (g , Subtype=-out Trunc-level p)}) s
