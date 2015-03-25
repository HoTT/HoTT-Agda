{-# OPTIONS --without-K #-}

open import HoTT
open import lib.cubical.elims.CubeMove

module lib.cubical.elims.SuspCofSection where

{- If f : X → Y is a section, then to prove two functions
 - u v : ΣCof(f) → C are equal, it suffices to show they agree
 - on north, south, and merid∘cfcod. -}

module _ {i j k} {X : Ptd i} {Y : Ptd j} {C : Type k}
  (f : fst (X ⊙→ Y)) (g : fst Y → fst X)
  (inv : ∀ x → g (fst f x) == x)
  {u v : Suspension (Cofiber (fst f)) → C}
  (north* : u (north _) == v (north _))
  (south* : u (south _) == v (south _))
  (cod* : (y : fst Y) → Square north* (ap u (merid _ (cfcod _ y)))
                               (ap v (merid _ (cfcod _ y))) south*)
  where

  susp-cof-section-path-elim : (σ : fst (⊙Susp (⊙Cof f))) → u σ == v σ
  susp-cof-section-path-elim = Suspension-elim _ north* south* coh
    where
    SquareType : fst (⊙Cof f) → Type _
    SquareType κ = Square north* (ap u (merid _ κ)) (ap v (merid _ κ)) south*

    base* = transport SquareType (! (cfglue _ (snd X))) (cod* (fst f (snd X)))

    CubeType : (x : fst X)
      → SquareType (cfcod _ (fst f x)) → Type _
    CubeType x sq =
      Cube base* sq
        (natural-square (λ _ → north*) (cfglue _ x))
        (natural-square (ap u ∘ merid _) (cfglue _ x))
        (natural-square (ap v ∘ merid _) (cfglue _ x))
        (natural-square (λ _ → south*) (cfglue _ x))

    fill : (x : fst X) (sq : SquareType (cfcod _ (fst f x)))
      → Σ (Square north* idp idp north*) (λ p → CubeType x (p ⊡h sq))
    fill x sq = (fst fill' , cube-right-from-front (fst fill') sq (snd fill'))
      where
      fill' = fill-cube-right _ _ _ _ _

    coh : (κ : fst (⊙Cof f))
      → north* == south* [ (λ σ → u σ == v σ) ↓ merid _ κ ]
    coh = ↓-='-from-square ∘ Cofiber-elim _
      base*
      (λ y → fst (fill (g y) (cod* (fst f (g y)))) ⊡h cod* y)
      (cube-to-↓-square ∘ λ x → transport
        (λ w → CubeType x (fst (fill w (cod* (fst f w))) ⊡h cod* (fst f x)))
        (! (inv x))
        (snd (fill _ _)))
