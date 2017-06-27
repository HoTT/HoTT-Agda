{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.HSpace where

-- This is just an approximation because
-- not all higher cells are killed.
record HSpaceStructure {i} (X : Ptd i) : Type i where
  constructor hSpaceStructure
  field
    ⊙μ : (X ⊙× X) ⊙→ X

  μ : de⊙ X → de⊙ X → de⊙ X
  μ = curry (fst ⊙μ)

  field
    ⊙unit-l : ⊙μ ⊙∘ ⊙×-inr X X ⊙∼ ⊙idf X
    ⊙unit-r : ⊙μ ⊙∘ ⊙×-inl X X ⊙∼ ⊙idf X

  unit-l : ∀ x → μ (pt X) x == x
  unit-l = fst ⊙unit-l

  unit-r : ∀ x → μ x (pt X) == x
  unit-r = fst ⊙unit-r

  coh : unit-l (pt X) == unit-r (pt X)
  coh = ! (↓-idf=cst-out (snd ⊙unit-l) ∙ ∙-unit-r _)
      ∙ (↓-idf=cst-out (snd ⊙unit-r) ∙ ∙-unit-r _)

record AlternativeHSpaceStructure {i} (X : Ptd i) : Type i where
  constructor hSpaceStructure
  field
    μ : de⊙ X → de⊙ X → de⊙ X
    unit-l : ∀ x → μ (pt X) x == x
    unit-r : ∀ x → μ x (pt X) == x
    coh : unit-l (pt X) == unit-r (pt X)

  ⊙μ : (X ⊙× X) ⊙→ X
  ⊙μ = uncurry μ , unit-l (pt X)

  ⊙unit-l : ⊙μ ⊙∘ ⊙×-inr X X ⊙∼ ⊙idf X
  ⊙unit-l = unit-l , ↓-idf=cst-in' idp

  ⊙unit-r : ⊙μ ⊙∘ ⊙×-inl X X ⊙∼ ⊙idf X
  ⊙unit-r = unit-r , ↓-idf=cst-in' coh

from-alt-h-space : ∀ {i} {X : Ptd i} → AlternativeHSpaceStructure X → HSpaceStructure X
from-alt-h-space hss = record {AlternativeHSpaceStructure hss}

to-alt-h-space : ∀ {i} {X : Ptd i} → HSpaceStructure X → AlternativeHSpaceStructure X
to-alt-h-space hss = record {HSpaceStructure hss}

module ConnectedHSpace {i} {X : Ptd i} (c : is-connected 0 (de⊙ X))
  (hX : HSpaceStructure X) where

  open HSpaceStructure hX public

  {-
  Given that [X] is 0-connected, to prove that each [μ x] is an equivalence we
  only need to prove that one of them is. But for [x] = [pt X], [μ x] is the
  identity so we’re done.
  -}

  l-is-equiv : ∀ x → is-equiv (λ y → μ y x)
  l-is-equiv = prop-over-connected {a = pt X} c
    (λ x → (is-equiv (λ y → μ y x) , is-equiv-is-prop))
    (transport! is-equiv (λ= unit-r) (idf-is-equiv _))

  r-is-equiv : ∀ x → is-equiv (λ y → μ x y)
  r-is-equiv = prop-over-connected {a = pt X} c
    (λ x → (is-equiv (λ y → μ x y) , is-equiv-is-prop))
    (transport! is-equiv (λ= unit-l) (idf-is-equiv _))

  l-equiv : de⊙ X → de⊙ X ≃ de⊙ X
  l-equiv x = _ , l-is-equiv x

  r-equiv : de⊙ X → de⊙ X ≃ de⊙ X
  r-equiv x = _ , r-is-equiv x
