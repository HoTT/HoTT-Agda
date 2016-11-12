{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.JoinComm where

module _ {i j} {A : Type i} {B : Type j} where

  swap : A * B → B * A
  swap = Swap.f  module _ where

    swap-glue : (a : A) (b : B) → right a == left b
    swap-glue a b = ! (glue (b , a))

    module Swap = PushoutRec right left (uncurry swap-glue)

{- ∞TT:

  swap : A * B → B * A
  swap (left a) = right a
  swap (right b) = left b
  ap swap (glue (a , b)) = ! (glue (b , a))
-}

module _ {i j} {A : Type i} {B : Type j} where

  swap-swap : (x : A * B) → swap (swap x) == x
  swap-swap = Pushout-elim (λ a → idp) (λ b → idp)
    (λ c → ↓-∘=idf-in' swap swap {p = glue c} (swap-swap-glue c)) where

    swap-swap-glue : (c : A × B) → ap swap (ap swap (glue c)) == glue c
    swap-swap-glue (a , b) =
      ap swap (ap swap (glue (a , b)))   =⟨ Swap.glue-β (a , b) |in-ctx ap swap ⟩
      ap swap (! (glue (b , a)))         =⟨ ap-! swap (glue (b , a)) ⟩
      ! (ap swap (glue (b , a)))         =⟨ Swap.glue-β (b , a) |in-ctx ! ⟩
      ! (! (glue (a , b)))               =⟨ !-! (glue (a , b)) ⟩
      glue (a , b) ∎

{- ∞TT:

  swap-swap : (x : A * B) → swap (swap x) == x
  swap-swap (left a) = idp
  swap-swap (right b) = idp
  apd swap-swap (glue (a , b)) = !-! (glue (a , b))
-}

module _ {i j} {A : Type i} {B : Type j} where

  swap-equiv : (A * B) ≃ (B * A)
  swap-equiv = equiv swap swap swap-swap swap-swap

  *-comm = swap-equiv
