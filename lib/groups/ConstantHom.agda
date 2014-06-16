{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Group

module lib.groups.ConstantHom where

cst-hom : ∀ {i j} {G : Group i} {H : Group j} → GroupHom G H
cst-hom {H = H} = group-hom (cst ident) idp (λ _ _ → ! (unitl _))
  where open Group H

pre∘-cst-hom : ∀ {i j k} {G : Group i} {H : Group j} {K : Group k}
  (φ : GroupHom H K)
  → φ ∘hom cst-hom {G = G} {H = H} == cst-hom
pre∘-cst-hom φ = hom= _ _ (λ= (λ g → GroupHom.pres-ident φ))
