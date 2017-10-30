{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.PathSetIsInitalCover {i} (X : Ptd i)
    -- and an arbitrary covering
    {k} (⊙cov : ⊙Cover X k) where

  open Cover

  private
    univ-cover = path-set-cover X
    module ⊙cov = ⊙Cover ⊙cov

  -- Weak initiality by transport.
  quotient-cover : CoverHom univ-cover ⊙cov.cov
  quotient-cover _ p = cover-trace ⊙cov.cov ⊙cov.pt p

  -- Strong initiality by path induction.
  module Uniqueness
    (cover-hom : CoverHom univ-cover ⊙cov.cov)
    (pres-pt : cover-hom (pt X) idp₀ == ⊙cov.pt)
    where

    private
      lemma₁ : ∀ a p → cover-hom a [ p ] == quotient-cover a [ p ]
      lemma₁ ._ idp = pres-pt

      lemma₂ : ∀ a p → cover-hom a p == quotient-cover a p
      lemma₂ a = Trunc-elim
        (lemma₁ a)

    theorem : cover-hom == quotient-cover
    theorem = λ= λ a → λ= $ lemma₂ a
