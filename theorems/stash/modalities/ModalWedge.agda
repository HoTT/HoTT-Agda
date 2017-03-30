{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import stash.modalities.Modalities
open import stash.modalities.FiberOfWedgeToProduct

module stash.modalities.ModalWedge {i} (M : Modality {i})
  {A : Type i} {a₀ : A} {B : Type i} {b₀ : B} where

  open Modality M

  -- Yeah, this is only going to be true if A and B are
  -- connected.  But then why does it work for truncation?
  
  record args : Type (lsucc i) where
    field
      jn-conn : is-◯-connected M ((a₀ == a₀) * (b₀ == b₀))
      R : A → B → ◯-Type M
      f : (a : A) → fst (R a b₀)
      g : (b : B) → fst (R a₀ b)
      p : f a₀ == g b₀

  module _ (r : args) where
    open args r

    private
      A⊙×B = ⊙[ A , a₀ ] ⊙× ⊙[ B , b₀ ]

    R' : de⊙ A⊙×B → ◯-Type M
    R' (a , b) = R a b

    ∨-to-×-is-◯-equiv : is-◯-equiv M (∨-to-× ⊙[ A , a₀ ] ⊙[ B , b₀ ])
    ∨-to-×-is-◯-equiv = {!transport (is-◯-connected M) ? ?!}

    -- fiber-of-∨-to-× ⊙[ A , a₀ ] ⊙[ B , b₀ ]

    ext : (a : A) → (b : B) → fst (R a b)
    ext a b = ◯-extend M (∨-to-× ⊙[ A , a₀ ] ⊙[ B , b₀ ]) {!!} R' {!!} {!!}




  
