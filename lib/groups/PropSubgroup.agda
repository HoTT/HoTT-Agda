{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Group
open import lib.types.Sigma
open import lib.types.Truncation
open import lib.groups.Homomorphisms

module lib.groups.PropSubgroup where

module _ {i} (G : Group i) where

  private
    module G = Group G

  module PropSubgroup {j} (P : G.El → Type j)
    (P-level : ∀ g → has-level ⟨-1⟩ (P g))
    (P-ident : P G.ident) (P-inv : ∀ {g} → P g → P (G.inv g))
    (P-comp : ∀ {g₁ g₂} → P g₁ → P g₂ → P (G.comp g₁ g₂)) where

    struct : GroupStructure (Σ G.El P)
    struct = record {
      ident = (G.ident , P-ident);
      inv = λ {(g , p) → (G.inv g , P-inv p)};
      comp = λ {(g₁ , p₁) (g₂ , p₂) → (G.comp g₁ g₂ , P-comp p₁ p₂)};
      unitl = λ {(g , _) →
        pair= (G.unitl g) (prop-has-all-paths-↓ (P-level _))};
      unitr = λ {(g , _) →
        pair= (G.unitr g) (prop-has-all-paths-↓ (P-level _))};
      assoc = λ {(g₁ , _) (g₂ , _) (g₃ , _) →
        pair= (G.assoc g₁ g₂ g₃) (prop-has-all-paths-↓ (P-level _))};
      invl = λ {(g , _) →
        pair= (G.invl g) (prop-has-all-paths-↓ (P-level _))};
      invr = λ {(g , _) →
        pair= (G.invr g) (prop-has-all-paths-↓ (P-level _))}}

    Subgroup : Group (lmax i j)
    Subgroup = group _ (Σ-level G.El-level (raise-level _ ∘ P-level)) struct

    inj : GroupHom Subgroup G
    inj = record {
      f = λ {(g , _) → g};
      pres-comp = λ _ _ → idp}

    module _ {j} {H : Group j} (φ : GroupHom H G) where

      private
        module H = Group H
        module φ = GroupHom φ

      prop-hom : Π H.El (P ∘ φ.f) → GroupHom H Subgroup
      prop-hom p = record {
        f = λ g → (φ.f g , p g);
        pres-comp = λ g₁ g₂ →
          pair= (φ.pres-comp g₁ g₂) (prop-has-all-paths-↓ (P-level _))}

module _ {i} {j} {G : Group i} {H : Group j} (φ : GroupHom G H) where

  private
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

    module Ker = PropSubgroup G (λ g → φ.f g == H.ident)
      (λ g → H.El-level _ _) φ.pres-ident
      (λ p → φ.pres-inv _ ∙ ap H.inv p ∙ group-inv-ident H)
      (λ p₁ p₂ → φ.pres-comp _ _ ∙ ap2 H.comp p₁ p₂ ∙ H.unitl _)

    module Im = PropSubgroup H (λ h → Trunc ⟨-1⟩ (Σ G.El (λ g → φ.f g == h)))
      (λ h → Trunc-level) ([ G.ident , φ.pres-ident ])
      (Trunc-fmap (λ {(g , p) →
        (G.inv g , φ.pres-inv g ∙ ap H.inv p)}))
      (Trunc-fmap2 (λ {(g₁ , p₁) (g₂ , p₂) →
        (G.comp g₁ g₂ , φ.pres-comp g₁ g₂ ∙ ap2 H.comp p₁ p₂)}))

  open Ker public renaming
    (struct to ker-struct; Subgroup to Ker;
     inj to ker-inj; prop-hom to ker-hom)


  open Im public renaming
    (struct to im-struct; Subgroup to Im;
     inj to im-inj; prop-hom to im-out-hom)

  im-in-hom : GroupHom G Im
  im-in-hom = record {
    f = λ g → (φ.f g , [ g , idp ]);
    pres-comp = λ g₁ g₂ →
      pair= (φ.pres-comp g₁ g₂) (prop-has-all-paths-↓ Trunc-level)}

  im-in-surj : (h : Group.El Im)
    → Trunc ⟨-1⟩ (Σ G.El (λ g → GroupHom.f im-in-hom g == h))
  im-in-surj (_ , s) = Trunc-fmap (λ {(g , p) →
    (g , pair= p (prop-has-all-paths-↓ Trunc-level))}) s
