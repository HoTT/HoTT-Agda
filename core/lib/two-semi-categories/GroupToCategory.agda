{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Group
open import lib.groups.Homomorphism
open import lib.types.TwoSemiCategory
open import lib.two-semi-categories.Functor
open import lib.two-semi-categories.DualCategory

module lib.two-semi-categories.GroupToCategory where

group-to-cat : ∀ {i} → Group i → TwoSemiCategory lzero i
group-to-cat G =
  record
  { El = ⊤
  ; Arr = λ _ _ → G.El
  ; Arr-level = λ _ _ → raise-level 0 G.El-level
  ; two-semi-cat-struct =
    record
    { comp = G.comp
    ; assoc = G.assoc
    ; pentagon-identity = λ _ _ _ _ → =ₛ-in (prop-path (has-level-apply G.El-level _ _) _ _)
    }
  }
  where
    module G = Group G

homomorphism-to-functor : ∀ {i j} {G : Group i} {H : Group j}
  → G →ᴳ H
  → TwoSemiFunctor (group-to-cat G) (group-to-cat H)
homomorphism-to-functor {G = G} {H = H} φ =
  record
  { F₀ = idf ⊤
  ; F₁ = φ.f
  ; pres-comp = φ.pres-comp
  ; pres-comp-coh = λ _ _ _ → =ₛ-in $ prop-path (has-level-apply H.El-level _ _) _ _
  }
  where
    module G = Group G
    module H = Group H
    module φ = GroupHom φ

ab-group-cat-to-dual : ∀ {i} (G : AbGroup i)
  → TwoSemiFunctor
      (group-to-cat (AbGroup.grp G))
      (dual-cat (group-to-cat (AbGroup.grp G)))
ab-group-cat-to-dual G =
  record
  { F₀ = λ _ → unit
  ; F₁ = λ g → g
  ; pres-comp = G.comm
  ; pres-comp-coh = λ _ _ _ → =ₛ-in $ prop-path (has-level-apply G.El-level _ _) _ _
  }
  where module G = AbGroup G
