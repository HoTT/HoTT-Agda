{-# OPTIONS --without-K #-}

{-
  Ribbon is the explicit covering space construction.

  This construction is given by Daniel Grayson, Favonia (me)
  and Guillaume Brunerie together.
-}

open import Base
open import Homotopy.Pointed

-- A is the pointed base space.
-- Y is intended to be a (group-)set,
-- but can be an arbitrarily weird space.
module Homotopy.Cover.Ribbon {i} (A⋆ : pType i) {Y : Set i} where
  open pType A⋆ renaming (∣_∣ to A ; ⋆ to a)

  open import Homotopy.Truncation
  open import Homotopy.PathTruncation
  open import Homotopy.HomotopyGroups
  open import Algebra.GroupSets (fundamental-group A⋆)

  -- The HIT ribbon---reconstructed covering space
  private
    module Ribbon {act : action Y} where
      open action act

      private
        data #ribbon (a₂ : A) : Set i where
          #trace : Y →  a ≡₀ a₂ → #ribbon a₂

      ribbon : A → Set i
      ribbon = #ribbon

      -- A point in the fiber a₂.
      {-
        y is a point in the fiber a, and
        p is a path to transport y to fiber a₂.
      -}
      trace : ∀ {a₂} → Y → a ≡₀ a₂ → ribbon a₂
      trace = #trace

      {-
        A loop based at a can used as a group action
        or for concatination.  Both should be equivalent.

        And after pasting, make the type fiberwise a set.
      -}
      postulate -- HIT
        paste : ∀ {a₂} y loop (p : a ≡₀ a₂)
          → trace (y ∙ loop) p ≡ trace y (loop ∘₀ p)
        ribbon-is-set : ∀ a₂ → is-set (ribbon a₂)

      -- Standard dependent eliminator
      ribbon-rec : ∀ a₂ {j} (P : ribbon a₂ → Set j)
        ⦃ P-is-set : ∀ r → is-set (P r) ⦄
        (trace* : ∀ y p → P (trace y p))
        (paste* : ∀ y loop p → transport P (paste y loop p) (trace* (y ∙ loop) p)
                             ≡ trace* y (loop ∘₀ p))
        → (∀ r → P r)
      ribbon-rec a₂ P trace* paste* (#trace y p) = trace* y p

      -- Standard non-dependent eliminator
      ribbon-rec-nondep : ∀ a₂ {j} (P : Set j)
        ⦃ P-is-set : is-set P ⦄
        (trace* : ∀ (y : Y) (p : a ≡₀ a₂) → P)
        (paste* : ∀ y (loop : a ≡₀ a) p → trace* (y ∙ loop) p ≡ trace* y (loop ∘₀ p))
        → (ribbon a₂ → P)
      ribbon-rec-nondep a₂ P trace* paste* (#trace y p) = trace* y p

  open Ribbon public hiding (ribbon)

  module _ (act : action Y) where

    ribbon : A → Set i
    ribbon = Ribbon.ribbon {act}

    trans-trace : ∀ {a₁ a₂} (q : a₁ ≡ a₂) y p
      → transport ribbon q (trace y p) ≡ trace y (p ∘₀ proj q)
    trans-trace (refl _) y p = ap (trace y) $ ! $ refl₀-right-unit p
