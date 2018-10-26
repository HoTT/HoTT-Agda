{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Group
open import lib.types.List
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Word
open import lib.groups.Homomorphism
open import lib.groups.GeneratedGroup
open import lib.groups.GeneratedAbelianGroup
open import lib.groups.Isomorphism

module lib.groups.TensorProduct where

module TensorProduct₀ {i} {j} (G : AbGroup i) (H : AbGroup j) where

  private
    module G = AbGroup G
    module H = AbGroup H

  ⊗-pair : Type (lmax i j)
  ⊗-pair = G.El × H.El

  data ⊗-rel : Word ⊗-pair → Word ⊗-pair → Type (lmax i j) where
    linear-l : (g₁ g₂ : G.El) (h : H.El) →
      ⊗-rel (inl (G.comp g₁ g₂ , h) :: nil) (inl (g₁ , h) :: inl (g₂ , h) :: nil)
    linear-r : (g : G.El) (h₁ h₂ : H.El) →
      ⊗-rel (inl (g , H.comp h₁ h₂) :: nil) (inl (g , h₁) :: inl (g , h₂) :: nil)

  private
    module Gen = GeneratedAbelianGroup ⊗-pair ⊗-rel
  open Gen hiding (GenGroup; GenAbGroup; El) public

  abstract
    abgroup : AbGroup (lmax i j)
    abgroup = Gen.GenAbGroup

  open AbGroup abgroup public

  abstract
    infixr 80 _⊗_
    _⊗_ : G.El → H.El → El
    _⊗_ g h = insert (g , h)

    ⊗-lin-l : ∀ g₁ g₂ h → G.comp g₁ g₂ ⊗ h == comp (g₁ ⊗ h) (g₂ ⊗ h)
    ⊗-lin-l g₁ g₂ h = rel-holds (linear-l g₁ g₂ h)

    ⊗-lin-r : ∀ g h₁ h₂ → g ⊗ H.comp h₁ h₂ == comp (g ⊗ h₁) (g ⊗ h₂)
    ⊗-lin-r g h₁ h₂ = rel-holds (linear-r g h₁ h₂)

    ⊗-ident-l : ∀ h → G.ident ⊗ h == ident
    ⊗-ident-l h = cancel-l (G.ident ⊗ h) $
      comp (G.ident ⊗ h) (G.ident ⊗ h)
        =⟨ ! (⊗-lin-l G.ident G.ident h) ⟩
      G.comp G.ident G.ident ⊗ h
        =⟨ ap (_⊗ h) (G.unit-l G.ident) ⟩
      G.ident ⊗ h
        =⟨ ! (unit-r (G.ident ⊗ h)) ⟩
      comp (G.ident ⊗ h) ident =∎

    ⊗-ident-r : ∀ g → g ⊗ H.ident == ident
    ⊗-ident-r g = cancel-r (g ⊗ H.ident) $
      comp (g ⊗ H.ident) (g ⊗ H.ident)
        =⟨ ! (⊗-lin-r g H.ident H.ident) ⟩
      g ⊗ H.comp H.ident H.ident
        =⟨ ap (g ⊗_) (H.unit-l H.ident) ⟩
      g ⊗ H.ident
        =⟨ ! (unit-r (g ⊗ H.ident)) ⟩
      comp (g ⊗ H.ident) ident =∎

  ins-l-hom : H.El → G.grp →ᴳ grp
  ins-l-hom h = group-hom (_⊗ h) (λ g₁ g₂ → ⊗-lin-l g₁ g₂ h)

  ins-r-hom : G.El → H.grp →ᴳ grp
  ins-r-hom g = group-hom (g ⊗_) (⊗-lin-r g)

  module BilinearMaps {k} (L : AbGroup k) where

    private
      module L = AbGroup L
      module HE = Gen.HomomorphismEquiv L

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
        f (g , h) = b.bmap g h
        f-respects : HE.respects-rel f
        f-respects (linear-l g₁ g₂ h) = b.linearity-l g₁ g₂ h
        f-respects (linear-r g h₁ h₂) = b.linearity-r g h₁ h₂
      from : HE.RelationRespectingFunction → BilinearMap
      from (HE.rel-res-fun f f-respects) =
        record { bmap = bmap; linearity-l = linearity-l; linearity-r = linearity-r }
        where
        bmap : G.El → H.El → L.El
        bmap g h = f (g , h)
        linearity-l : is-linear-l bmap
        linearity-l g₁ g₂ h = f-respects (linear-l g₁ g₂ h)
        linearity-r : is-linear-r bmap
        linearity-r g h₁ h₂ = f-respects (linear-r g h₁ h₂)

  module UniversalProperty {k} (L : AbGroup k) where

    open BilinearMaps L public
    private
      module HE = Gen.HomomorphismEquiv L

    abstract
      extend-equiv : BilinearMap ≃ (grp →ᴳ AbGroup.grp L)
      extend-equiv =
        HE.extend-equiv ∘e bilinear-to-legal-equiv

      extend : BilinearMap → (grp →ᴳ AbGroup.grp L)
      extend = –> extend-equiv

      restrict : (grp →ᴳ AbGroup.grp L) → BilinearMap
      restrict = <– extend-equiv

      extend-β : ∀ b g h → GroupHom.f (extend b) (g ⊗ h) == BilinearMap.bmap b g h
      extend-β b g h = idp

      hom= : ∀ {ϕ ψ : grp →ᴳ AbGroup.grp L}
        → (∀ g h → GroupHom.f ϕ (g ⊗ h) == GroupHom.f ψ (g ⊗ h))
        → ϕ == ψ
      hom= {ϕ} {ψ} e =
        ϕ
          =⟨ ! (<–-inv-r extend-equiv ϕ) ⟩
        extend (restrict ϕ)
          =⟨ ap extend (BilinearMap= (λ= (λ g → λ= (λ h → e g h)))) ⟩
        extend (restrict ψ)
          =⟨ <–-inv-r extend-equiv ψ ⟩
        ψ =∎

module TensorProduct₁ {i} {j} (G : AbGroup i) (H : AbGroup j) where

  private
    module G⊗H = TensorProduct₀ G H
    module H⊗G = TensorProduct₀ H G
    module F = G⊗H.UniversalProperty H⊗G.abgroup

    b : F.BilinearMap
    b =
      record
      { bmap = λ g h → h H⊗G.⊗ g
      ; linearity-l = λ g₁ g₂ h → H⊗G.⊗-lin-r h g₁ g₂
      ; linearity-r = λ g h₁ h₂ → H⊗G.⊗-lin-l h₁ h₂ g
      }

  swap : (G⊗H.grp →ᴳ H⊗G.grp)
  swap = F.extend b

  swap-β : ∀ g h →
    GroupHom.f swap (g G⊗H.⊗ h) == h H⊗G.⊗ g
  swap-β g h = F.extend-β b g h

  open G⊗H public

module TensorProduct₂ {i} {j} (G : AbGroup i) (H : AbGroup j) where

  private
    module G⊗H = TensorProduct₁ G H
    module H⊗G = TensorProduct₁ H G

  swap-swap : ∀ s → GroupHom.f (H⊗G.swap ∘ᴳ G⊗H.swap) s == s
  swap-swap s =
    ap (λ ϕ → GroupHom.f ϕ s) $
    G⊗H.UniversalProperty.hom= G⊗H.abgroup {ϕ = H⊗G.swap ∘ᴳ G⊗H.swap} {ψ = idhom _} $
    λ g h → ap (GroupHom.f H⊗G.swap) (G⊗H.swap-β g h) ∙ H⊗G.swap-β h g

  swap-swap-idhom : H⊗G.swap ∘ᴳ G⊗H.swap == idhom G⊗H.grp
  swap-swap-idhom = group-hom= (λ= swap-swap)

  open G⊗H public

module TensorProduct {i} {j} (G : AbGroup i) (H : AbGroup j) where

  private
    module G⊗H = TensorProduct₂ G H
    module H⊗G = TensorProduct₂ H G

  swap-is-equiv : is-equiv (GroupHom.f G⊗H.swap)
  swap-is-equiv = is-eq _ (GroupHom.f H⊗G.swap) H⊗G.swap-swap G⊗H.swap-swap

  commutative : G⊗H.grp ≃ᴳ H⊗G.grp
  commutative = G⊗H.swap , swap-is-equiv

  open G⊗H public
