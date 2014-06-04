{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Cospan
open import lib.types.Pullback
open import lib.types.Group

module lib.groups.PullbackGroup where

--   φ   ψ
-- H → G ← K

record Group-Cospan {i j k : ULevel} : Type (lsucc (lmax (lmax i j) k)) where
  constructor ptd-cospan
  field
    H : Group i
    K : Group j
    G : Group k
    φ : GroupHom H G
    ψ : GroupHom K G

module _ {i j k} (H : Group i) (K : Group j) (G : Group k)
  (φ : GroupHom H G) (ψ : GroupHom K G) where

  private
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
        (grouphom-pres-inv φ h ∙ ap G.inv p ∙ ! (grouphom-pres-inv ψ k))};
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
    El-level = pullback-level ⟨0⟩ H.El-level K.El-level G.El-level;
    group-struct = Pullback-group-struct}
