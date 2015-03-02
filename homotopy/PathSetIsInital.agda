{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.PathSetIsInital {i} (A : Type i)
  (A-conn : is-connected ⟨0⟩ A) where

  open Cover

  module _
    (a₁ : A)
    -- And an arbitrary covering.
    {k} (cov : Cover A k)
    (cov-conn : is-connected ⟨0⟩ (Cover.TotalSpace cov))
    (a↑₁ : Fiber cov a₁)
    where

    private
      univ-cover = path-set-cover ⊙[ A , a₁ ]

    -- Weak initiality by transport.
    quotient-cover : CoverHom univ-cover cov
    quotient-cover _ p = cover-trace cov a↑₁ p

    -- Strong initiality by path induction.
    module Uniqueness
      (cover-hom : CoverHom univ-cover cov)
      (pres-a↑₁ : cover-hom a₁ idp₀ == a↑₁)
      where

      private
        lemma₁ : ∀ a p → cover-hom a [ p ] == quotient-cover a [ p ]
        lemma₁ ._ idp = pres-a↑₁

        lemma₂ : ∀ a p → cover-hom a p == quotient-cover a p
        lemma₂ a = Trunc-elim
          (λ p → =-preserves-level ⟨0⟩ (Cover.Fiber-level cov a))
          (lemma₁ a)

      theorem : cover-hom == quotient-cover
      theorem = λ= λ a → λ= $ lemma₂ a
