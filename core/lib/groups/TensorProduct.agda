{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Group
open import lib.types.List
open import lib.types.Pi
open import lib.types.Word
open import lib.groups.Homomorphism
open import lib.groups.GeneratedGroup
open import lib.groups.GeneratedAbelianGroup

module lib.groups.TensorProduct {i} {j} (G : AbGroup i) (H : AbGroup j) where

  record ⊗-pair : Type (lmax i j) where
    constructor _⊗_
    field
      ⊗-fst : AbGroup.El G
      ⊗-snd : AbGroup.El H

  private
    module G = AbGroup G
    module H = AbGroup H

  data ⊗-rel : Word ⊗-pair → Word ⊗-pair → Type (lmax i j) where
    linear-l : (g₁ g₂ : G.El) (h : H.El) →
      ⊗-rel (inl (G.comp g₁ g₂ ⊗ h) :: nil) (inl (g₁ ⊗ h) :: inl (g₂ ⊗ h) :: nil)
    linear-r : (g : G.El) (h₁ h₂ : H.El) →
      ⊗-rel (inl (g ⊗ H.comp h₁ h₂) :: nil) (inl (g ⊗ h₁) :: inl (g ⊗ h₂) :: nil)

  private
    module Gen = GeneratedAbelianGroup ⊗-pair ⊗-rel
  open Gen hiding (GenGroup; GenAbGroup) public

  TensorProduct : AbGroup (lmax i j)
  TensorProduct = Gen.GenAbGroup

  module TensorProduct = AbGroup TensorProduct

  module UniversalProperty {k} (L : AbGroup k) where

    private
      module HE = Gen.HomomorphismEquiv L
      module L = AbGroup L

    is-linear-l : (G.El → H.El → L.El) → Type (lmax i (lmax j k))
    is-linear-l b = ∀ g₁ g₂ h → b (G.comp g₁ g₂) h == L.comp (b g₁ h) (b g₂ h)

    is-linear-l-is-prop : (b : G.El → H.El → L.El) → is-prop (is-linear-l b)
    is-linear-l-is-prop b =
      Π-level $ λ g₁ →
      Π-level $ λ g₂ →
      Π-level $ λ h →
      has-level-apply L.El-level _ _

    is-linear-r : (G.El → H.El → L.El) → Type (lmax i (lmax j k))
    is-linear-r b = ∀ g h₁ h₂ → b g (H.comp h₁ h₂) == L.comp (b g h₁) (b g h₂)

    is-linear-r-is-prop : (b : G.El → H.El → L.El) → is-prop (is-linear-r b)
    is-linear-r-is-prop b =
      Π-level $ λ g →
      Π-level $ λ h₁ →
      Π-level $ λ h₂ →
      has-level-apply L.El-level _ _

    record BilinearMap : Type (lmax i (lmax j k)) where
      field
        bmap : G.El → H.El → L.El
        linearity-l : is-linear-l bmap
        linearity-r : is-linear-r bmap

    BilinearMap= : {b b' : BilinearMap}
      → BilinearMap.bmap b == BilinearMap.bmap b'
      → b == b'
    BilinearMap= {b} {b'} idp =
      ap2 mk-bilinear-map
        (prop-path (is-linear-l-is-prop b.bmap) b.linearity-l b'.linearity-l)
        (prop-path (is-linear-r-is-prop b.bmap) b.linearity-r b'.linearity-r)
      where
      module b  = BilinearMap b
      module b' = BilinearMap b'
      mk-bilinear-map : is-linear-l b.bmap → is-linear-r b.bmap → BilinearMap
      mk-bilinear-map lin-l lin-r =
        record { bmap = b.bmap; linearity-l = lin-l; linearity-r = lin-r }

    bilinear-to-legal-equiv : BilinearMap ≃ HE.RelationRespectingFunction
    bilinear-to-legal-equiv =
      equiv to from
            (λ lf → HE.RelationRespectingFunction= idp)
            (λ b  → BilinearMap= idp)
      where
      to : BilinearMap → HE.RelationRespectingFunction
      to b = HE.rel-res-fun f f-respects
        where
        module b = BilinearMap b
        f : ⊗-pair → L.El
        f (g ⊗ h) = b.bmap g h
        f-respects : HE.respects-rel f
        f-respects (linear-l g₁ g₂ h) = b.linearity-l g₁ g₂ h
        f-respects (linear-r g h₁ h₂) = b.linearity-r g h₁ h₂
      from : HE.RelationRespectingFunction → BilinearMap
      from (HE.rel-res-fun f f-respects) =
        record { bmap = bmap; linearity-l = linearity-l; linearity-r = linearity-r }
        where
        bmap : G.El → H.El → L.El
        bmap g h = f (g ⊗ h)
        linearity-l : is-linear-l bmap
        linearity-l g₁ g₂ h = f-respects (linear-l g₁ g₂ h)
        linearity-r : is-linear-r bmap
        linearity-r g h₁ h₂ = f-respects (linear-r g h₁ h₂)

    TensorProduct-extend-equiv : BilinearMap ≃ (TensorProduct.grp →ᴳ L.grp)
    TensorProduct-extend-equiv =
      HE.extend-equiv ∘e bilinear-to-legal-equiv

    TensorProduct-extend : BilinearMap → (TensorProduct.grp →ᴳ L.grp)
    TensorProduct-extend = –> TensorProduct-extend-equiv
