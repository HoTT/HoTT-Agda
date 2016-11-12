{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.PathSetIsInitalCover {i} (X : Ptd i)
    -- And an arbitrary covering
    {k} (cov : Cover (fst X) k)
    -- and a point.
    (pt↑ : Cover.Fiber cov (snd X)) where

  open Cover

  private
    univ-cover = path-set-cover X

  -- Weak initiality by transport.
  quotient-cover : CoverHom univ-cover cov
  quotient-cover _ p = cover-trace cov pt↑ p

  -- Strong initiality by path induction.
  module Uniqueness
    (cover-hom : CoverHom univ-cover cov)
    (pres-pt↑ : cover-hom (snd X) idp₀ == pt↑)
    where

    private
      lemma₁ : ∀ a p → cover-hom a [ p ] == quotient-cover a [ p ]
      lemma₁ ._ idp = pres-pt↑

      lemma₂ : ∀ a p → cover-hom a p == quotient-cover a p
      lemma₂ a = Trunc-elim
        (λ p → =-preserves-level 0 (Cover.Fiber-level cov a))
        (lemma₁ a)

    theorem : cover-hom == quotient-cover
    theorem = λ= λ a → λ= $ lemma₂ a
