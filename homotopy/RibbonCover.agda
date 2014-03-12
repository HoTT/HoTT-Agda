{-# OPTIONS --without-K #-}

{-
  Ribbon is the explicit covering space construction.

  This construction is given by Daniel Grayson, Favonia
  and Guillaume Brunerie together.
-}

open import HoTT

-- A is the pointed base space.
-- El is intended to be a (group-)set,
module homotopy.RibbonCover {i : ULevel} where

  -- The HIT ribbon---reconstructed covering space

  private
    module _ (A∙ : Ptd i) {j} (gs : Gset (concrete-fundamental-group A∙) j) where
      private
        A = fst A∙
        a = snd A∙
        El = Gset.El gs
        El-level = Gset.El-level gs

      data #Ribbon-aux (a₂ : A) : Type (lmax i j) where
        #trace : El → a =₀ a₂ → #Ribbon-aux a₂

      data #Ribbon (a₂ : A) : Type (lmax i j) where
        #ribbon : #Ribbon-aux a₂ → (Unit → Unit) → #Ribbon a₂

  Ribbon : ∀ (A∙ : Ptd i) {j} (gs : Gset (fundamental-group A∙) j)
    → fst A∙ → Type (lmax i j)
  Ribbon = #Ribbon

  module _ {A∙ : Ptd i} {j} {gs : Gset (fundamental-group A∙) j} {a₂ : fst A∙} where
    private
      A = fst A∙
      a = snd A∙
      El = Gset.El gs
      El-level = Gset.El-level gs
      _⊙_ = Gset.act gs

    -- A point in the fiber [a₂].
    {-
      [e] is a point in the [fiber a], and
      [p] is a path to transport [y] to fiber [a₂].
    -}
    trace : El → a =₀ a₂ → Ribbon A∙ gs a₂
    trace el p = #ribbon (#trace el p) _

    {-
      A loop based at [a] can used as a group action
      or for concatination.  Both should be equivalent.
    -}
    postulate -- HIT
      paste : ∀ el loop (p : a =₀ a₂)
        → trace (el ⊙ loop) p == trace el (loop ∙₀ p)

    {-
      Make each fiber a set and cancel all higher structures
      due to [paste].
    -}
    postulate -- HIT
      Ribbon-is-set : is-set (Ribbon A∙ gs a₂)

    Ribbon-level = Ribbon-is-set

    -- Elimination rules.
    module RibbonElim {j} {P : Ribbon A∙ gs a₂ → Type j}
      (P-level : ∀ {r} → is-set (P r))
      (trace* : ∀ el p → P (trace el p))
      (paste* : ∀ el loop p
                → trace* (el ⊙ loop) p == trace* el (loop ∙₀ p)
                  [ P ↓ paste el loop p ]) where

      f : Π (Ribbon A∙ gs a₂) P
      f = f-aux phantom phantom where

        f-aux : Phantom trace* → Phantom paste* → Π (Ribbon A∙ gs a₂) P
        f-aux phantom phantom (#ribbon (#trace el p) _) = trace* el p

    open RibbonElim public using () renaming (f to Ribbon-elim)

    module RibbonRec {j} {P : Type j}
      (P-level : is-set P)
      (trace* : ∀ el p → P)
      (paste* : ∀ el loop p
                → trace* (el ⊙ loop) p == trace* el (loop ∙₀ p)) where

      private
        module M = RibbonElim P-level trace*
          (λ el loop p → ↓-cst-in (paste* el loop p))

      f : Ribbon A∙ gs a₂ → P
      f = M.f

    open RibbonRec public using () renaming (f to Ribbon-rec)

  -- This data structure gives a cover.
  Ribbon-cover : ∀ (A∙ : Ptd i) {j} (gs : Gset (fundamental-group A∙) j)
    → Cover (fst A∙) (lmax i j)
  Ribbon-cover A∙ gs = record
    { Fiber = Ribbon A∙ gs
    ; Fiber-level = λ a → Ribbon-level
    }

  trans-trace : ∀ {A : Type i} {a₁} {j}
    {gs : Gset (fundamental-group (A , a₁)) j}
    {a₂} (q : a₁ == a₂) y p
    → transport (Ribbon (A , a₁) gs) q (trace y p) == trace y (p ∙₀ [ q ])
  trans-trace idp y p = ap (trace y) $ ! $ ∙₀-unit-r p
