{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import lib.types.TwoSemiCategory

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

module ConnectedHSpace {i} {X : Ptd i} {{_ : is-connected 0 (de⊙ X)}}
  (hX : HSpaceStructure X) where

  open HSpaceStructure hX public

  {-
  Given that [X] is 0-connected, to prove that each [μ x] is an equivalence we
  only need to prove that one of them is. But for [x] = [pt X], [μ x] is the
  identity so we’re done.
  -}

  l-is-equiv : ∀ x → is-equiv (λ y → μ y x)
  l-is-equiv = prop-over-connected {a = pt X}
    (λ x → (is-equiv (λ y → μ y x) , is-equiv-is-prop))
    (transport! is-equiv (λ= unit-r) (idf-is-equiv _))

  r-is-equiv : ∀ x → is-equiv (λ y → μ x y)
  r-is-equiv = prop-over-connected {a = pt X}
    (λ x → (is-equiv (λ y → μ x y) , is-equiv-is-prop))
    (transport! is-equiv (λ= unit-l) (idf-is-equiv _))

  l-equiv : de⊙ X → de⊙ X ≃ de⊙ X
  l-equiv x = _ , l-is-equiv x

  r-equiv : de⊙ X → de⊙ X ≃ de⊙ X
  r-equiv x = _ , r-is-equiv x

module _ {i} {X : Ptd i} (hX : HSpaceStructure X) where

  module hX = HSpaceStructure hX

  associator : Type i
  associator = ∀ a b c → hX.μ (hX.μ a b) c == hX.μ a (hX.μ b c)

  coh-unit-r-eq : associator → de⊙ X → de⊙ X → Type i
  coh-unit-r-eq assoc a b = hX.unit-r (hX.μ a b) == assoc a b (pt X) ∙ ap (hX.μ a) (hX.unit-r b)

  coh-unit-r : associator → Type i
  coh-unit-r assoc = ∀ a b → coh-unit-r-eq assoc a b

  coh-unit-l-r-pentagon : associator → Type i
  coh-unit-l-r-pentagon assoc = ∀ a' →
    hX.unit-r (hX.μ (pt X) a') ∙ hX.unit-l a' ==
    assoc (pt X) a' (pt X) ∙ hX.unit-l (hX.μ a' (pt X)) ∙ hX.unit-r a'

  coh-unit-r-to-unit-l-r-pentagon : (assoc : associator)
    → coh-unit-r assoc → coh-unit-l-r-pentagon assoc
  coh-unit-r-to-unit-l-r-pentagon assoc c a' =
    hX.unit-r (hX.μ (pt X) a') ∙ hX.unit-l a'
      =⟨ ap (λ v → v ∙ hX.unit-l a') (c (pt X) a') ⟩
    (assoc (pt X) a' (pt X) ∙ ap (hX.μ (pt X)) (hX.unit-r a')) ∙ hX.unit-l a'
      =⟨ ∙-assoc (assoc (pt X) a' (pt X)) (ap (hX.μ (pt X)) (hX.unit-r a')) (hX.unit-l a') ⟩
    assoc (pt X) a' (pt X) ∙ ap (hX.μ (pt X)) (hX.unit-r a') ∙ hX.unit-l a'
      =⟨ ap (λ v → assoc (pt X) a' (pt X) ∙ v)
            (homotopy-naturality-to-idf (hX.μ (pt X)) hX.unit-l (hX.unit-r a')) ⟩
    assoc (pt X) a' (pt X) ∙ hX.unit-l (hX.μ a' (pt X)) ∙ hX.unit-r a' ∎

  coh-assoc-pentagon-eq : (assoc : associator) → (a b c d : de⊙ X) → Type i
  coh-assoc-pentagon-eq assoc a b c d =
    assoc (hX.μ a b) c d ◃∙ assoc a b (hX.μ c d) ◃∎
    =ₛ
    ap (λ s → hX.μ s d) (assoc a b c) ◃∙ assoc a (hX.μ b c) d ◃∙ ap (hX.μ a) (assoc b c d) ◃∎

  coh-assoc-pentagon : (assoc : associator) → Type i
  coh-assoc-pentagon assoc = ∀ a b c d → coh-assoc-pentagon-eq assoc a b c d

  HSpace-2-semi-category : {{X-level : has-level 1 (de⊙ X)}}
    → (assoc : associator)
    → coh-assoc-pentagon assoc
    → TwoSemiCategory lzero i
  HSpace-2-semi-category assoc assoc-coh =
    record
    { El = ⊤
    ; Arr = λ _ _ → de⊙ X
    ; Arr-level = λ _ _ → ⟨⟩
    ; two-semi-cat-struct =
      record
      { comp = hX.μ
      ; assoc = assoc
      ; pentagon-identity = assoc-coh
      }
    }
