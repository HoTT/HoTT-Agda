{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Cospan
open import lib.types.Pullback
open import lib.types.Group
open import lib.groups.Homomorphisms

module lib.groups.PullbackGroup where

--   φ   ψ
-- H → G ← K

record Group-Cospan {i j k : ULevel} : Type (lsucc (lmax (lmax i j) k)) where
  constructor group-cospan
  field
    H : Group i
    K : Group j
    G : Group k
    φ : H →ᴳ G
    ψ : K →ᴳ G

group-cospan-out : ∀ {i j k} → Group-Cospan {i} {j} {k} → Cospan {i} {j} {k}
group-cospan-out (group-cospan H K G φ ψ) =
  cospan (Group.El H) (Group.El K) (Group.El G) (GroupHom.f φ) (GroupHom.f ψ)


module _ {i j k} (D : Group-Cospan {i} {j} {k}) where

  private
    open Group-Cospan D
    module H = Group H
    module K = Group K
    module G = Group G
    module φ = GroupHom φ
    module ψ = GroupHom ψ

    d : Cospan
    d = cospan H.El K.El G.El φ.f ψ.f

  Pullback-group-struct : GroupStructure (Pullback d)
  Pullback-group-struct = record {
    ident = pullback H.ident K.ident (φ.pres-ident ∙ ! (ψ.pres-ident));
    inv = λ {(pullback h k p) →
      pullback (H.inv h) (K.inv k)
        (φ.pres-inv h ∙ ap G.inv p ∙ ! (ψ.pres-inv k))};
    comp = λ {(pullback h₁ k₁ p₁) (pullback h₂ k₂ p₂) →
      pullback (H.comp h₁ h₂) (K.comp k₁ k₂)
        (φ.pres-comp h₁ h₂ ∙ ap2 G.comp p₁ p₂ ∙ ! (ψ.pres-comp k₁ k₂))};
    unitl = λ {(pullback h k p) →
      pullback= d (H.unitl h) (K.unitl k)
        (prop-has-all-paths (G.El-level _ _) _ _)};
    unitr = λ {(pullback h k p) →
      pullback= d (H.unitr h) (K.unitr k)
        (prop-has-all-paths (G.El-level _ _) _ _)};
    assoc = λ {(pullback h₁ k₁ p₁) (pullback h₂ k₂ p₂) (pullback h₃ k₃ p₃) →
      pullback= d (H.assoc h₁ h₂ h₃) (K.assoc k₁ k₂ k₃)
        (prop-has-all-paths (G.El-level _ _) _ _)};
    invl = λ {(pullback h k p) →
      pullback= d (H.invl h) (K.invl k)
        (prop-has-all-paths (G.El-level _ _) _ _)};
    invr = λ {(pullback h k p) →
      pullback= d (H.invr h) (K.invr k)
        (prop-has-all-paths (G.El-level _ _) _ _)}}

  Pullback-Group : Group (lmax i (lmax j k))
  Pullback-Group = record {
    El = Pullback d;
    El-level = pullback-level 0 H.El-level K.El-level G.El-level;
    group-struct = Pullback-group-struct}

  pfst-hom : Pullback-Group →ᴳ H
  pfst-hom = record {
    f = Pullback.a;
    pres-comp = λ _ _ → idp}

  psnd-hom : Pullback-Group →ᴳ K
  psnd-hom = record {
    f = Pullback.b;
    pres-comp = λ _ _ → idp}

  module _ {l} {J : Group l} (χ : J →ᴳ H) (θ : J →ᴳ K) where

    private
      module χ = GroupHom χ
      module θ = GroupHom θ

    pullback-hom : ((j : Group.El J) → φ.f (χ.f j) == ψ.f (θ.f j))
      → J →ᴳ Pullback-Group
    pullback-hom p = record {
      f = λ j → pullback (χ.f j) (θ.f j) (p j);
      pres-comp = λ j₁ j₂ → pullback= (group-cospan-out D)
        (χ.pres-comp j₁ j₂)
        (θ.pres-comp j₁ j₂)
        (prop-has-all-paths (Group.El-level G _ _) _ _)}
