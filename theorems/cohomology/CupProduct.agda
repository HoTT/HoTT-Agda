{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane

module cohomology.CupProduct {i} (R : CRing i) where

  open CRing R
  open EMExplicit add-ab-group
  open EilenbergMacLane-functorial add-group add-group

  ⊙EM₀ : Ptd i
  ⊙EM₀ = ⊙[ El , zero ]

  {-
  cp₀₁ : ⊙EM₀ ⊙∧ ⊙EM₁ add-group ⊙→ ⊙EM₁ add-group
  cp₀₁ = f , idp
    where
      cp₀₁′ : El → EM₁ add-group → EM₁ add-group
      cp₀₁′ g = EM₁-fmap (mult-hom g)
      f : ⊙EM₀ ∧ ⊙EM₁ add-group → EM₁ add-group
      f = Smash-rec {C = EM₁ add-group} cp₀₁′ embase embase
                    (λ x → idp)
                    ?
                    -- (EM₁-elim {P = (λ x → cp₀₁′ zero x == embase)} idp ? ?)
  -}

  {-
  cp₀₁ : ⊙EM 0 ⊙∧ ⊙EM 1 ⊙→ ⊙EM 1
  cp₀₁ = Smash-rec {C = EM 1} cp₀₁′ ? {!!} {!!} {!!} , {!!}
    where
      cp₀₁′ : EM 0 → EM 1 → EM 1
      cp₀₁′ = {!!}
  -}
