{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import stash.modalities.Modalities

module stash.modalities.ModalWedge {i} (M : Modality {i})
  {A : Type i} {a₀ : A} {B : Type i} {b₀ : B} where

  open Modality M
  
  record args : Type (lsucc i) where
    field
      jn-conn : is-contr (◯ (a₀ == a₀) * (b₀ == b₀))
      R : A → B → P-Type M
      f : (a : A) → fst (R a b₀)
      g : (b : B) → fst (R a₀ b)
      p : f a₀ == g b₀

  -- I claim the above arguments should be enough to
  -- have an elimination.
  module _ (r : args) where
    open args r

    ext : (a : A) → (b : B) → fst (R a b)
    ext a = {!hfiber!}

  -- Intuitively, the reason is the following:
  --
  --   let ∨-to-× : X ∨ Y → X × Y be the inclusion of the wedge
  --   into the product.
  --
  --   Then I claim:
  --
  --   thm : (x : X) → (y : Y) → hfiber (∨-to-×) (x , y) ≃ (x == x) * (y == y)
  --


  
