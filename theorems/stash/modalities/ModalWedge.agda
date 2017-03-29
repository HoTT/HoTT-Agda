{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import stash.modalities.Modalities

module stash.modalities.ModalWedge {i} (M : Modality {i})
  {A : Type i} {a₀ : A} {B : Type i} {b₀ : B} where

  open Modality M
  
  record args : Type (lsucc i) where
    field
      jn-conn : is-contr (◯ ((a₀ == a₀) * (b₀ == b₀)))
      R : A → B → P-Type M
      f : (a : A) → fst (R a b₀)
      g : (b : B) → fst (R a₀ b)
      p : f a₀ == g b₀


  -- I claim the above arguments should be enough to
  -- have an elimination.
  module _ (r : args) where
    open args r

    ∨-to-× : ⊙[ A , a₀ ] ∨ ⊙[ B , b₀ ] → A × B 
    ∨-to-× = Wedge-rec (λ a → (a , b₀)) (λ b → (a₀ , b)) idp

    ∨-to-×-fiber-to : hfiber ∨-to-× (a₀ , b₀) → (a₀ == a₀) * (b₀ == b₀)
    ∨-to-×-fiber-to (w , p) = {!!}

    ∨-to-×-fiber-from : (a₀ == a₀) * (b₀ == b₀) → hfiber ∨-to-× (a₀ , b₀)
    ∨-to-×-fiber-from = Join-rec {!!} {!!} {!!}

    ∨-to-×-fiber : hfiber ∨-to-× (a₀ , b₀) ≃ (a₀ == a₀) * (b₀ == b₀)
    ∨-to-×-fiber = {!!}


    ext : (a : A) → (b : B) → fst (R a b)
    ext a = {!hfiber!}




  
