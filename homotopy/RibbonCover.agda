{-# OPTIONS --without-K #-}

{-
  Ribbon is the explicit covering space construction.

  This construction is given by Daniel Grayson, Favonia
  and Guillaume Brunerie together.
-}

open import HoTT

-- A is the pointed base space.
-- El is intended to be a (group-)set,
module homotopy.RibbonCover {i} (A∙ : Ptd i)
  {j} (gs : Gset (fundamental-group A∙) j) where

  private
    A = fst A∙
    a = snd A∙
    El = Gset.El gs
    El-level = Gset.El-level gs
    _⊙_ = Gset.act gs

  -- The HIT ribbon---reconstructed covering space
  private
    data #Ribbon-aux (a₂ : A) : Type (lmax i j) where
      #trace : El → a =₀ a₂ → #Ribbon-aux a₂

    data #Ribbon (a₂ : A) : Type (lmax i j) where
      #ribbon : #Ribbon-aux a₂ → (Unit → Unit) → #Ribbon a₂

  Ribbon : A → Type (lmax i j)
  Ribbon = #Ribbon

  -- A point in the fiber [a₂].
  {-
    [e] is a point in the [fiber a], and
    [p] is a path to transport [y] to fiber [a₂].
  -}
  trace : ∀ {a₂} → El → a =₀ a₂ → Ribbon a₂
  trace el p = #ribbon (#trace el p) _

  {-
    A loop based at [a] can used as a group action
    or for concatination.  Both should be equivalent.
  -}
  postulate -- HIT
    paste : ∀ {a₂} el loop (p : a =₀ a₂)
      → trace (el ⊙ loop) p == trace el (loop ∙₀ p)

  {-
    Make each fiber a set and cancel all higher structures
    due to [paste].
  -}
  postulate -- HIT
    Ribbon-is-set : ∀ {a₂} → is-set (Ribbon a₂)

  Ribbon-level = Ribbon-is-set

  -- Elimination rules.
  module RibbonElim a₂ {j} {P : Ribbon a₂ → Type j}
    (P-level : ∀ {r} → is-set (P r))
    (trace* : ∀ el p → P (trace el p))
    (paste* : ∀ el loop p
              → trace* (el ⊙ loop) p == trace* el (loop ∙₀ p)
                [ P ↓ paste el loop p ]) where

    f : Π (Ribbon a₂) P
    f = f-aux phantom phantom where

      f-aux : Phantom trace* → Phantom paste* → Π (Ribbon a₂) P
      f-aux phantom phantom (#ribbon (#trace el p) _) = trace* el p

  open RibbonElim public using () renaming (f to Ribbon-elim)

  module RibbonRec a₂ {j} {P : Type j}
    (P-level : is-set P)
    (trace* : ∀ el p → P)
    (paste* : ∀ el loop p
              → trace* (el ⊙ loop) p == trace* el (loop ∙₀ p)) where

    private
      module M = RibbonElim a₂ P-level trace*
        (λ el loop p → ↓-cst-in (paste* el loop p))

    f : Ribbon a₂ → P
    f = M.f

{-
  -- Code from the old library

  module _ (act : action Y) where

    ribbon : A → Set i
    ribbon = Ribbon.ribbon {act}

    trans-trace : ∀ {a₁ a₂} (q : a₁ ≡ a₂) y p
      → transport ribbon q (trace y p) ≡ trace y (p ∘₀ proj q)
    trans-trace refl y p = ap (trace y) $ ! $ refl₀-right-unit p
-}
