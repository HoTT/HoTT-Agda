{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.SuspProduct
open import homotopy.SuspSmash
open import homotopy.JoinSusp
open import cohomology.OrdinaryTheory

module cohomology.SphereProduct {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT
open import cohomology.Wedge OT

module _ (n : ℤ) (m : ℕ) (X : Ptd i) where

  private

    space-path : Ptd-Susp (Ptd-Sphere {i} m ×ptd X)
              == Ptd-Wedge (Ptd-Sphere {i} (S m))
                           (Ptd-Wedge (Ptd-Susp^ (S m) X) (Ptd-Susp X))
    space-path =
      SuspProduct.ptd-path (Ptd-Sphere m) X
      ∙ ap (λ Z → Ptd-Wedge (Ptd-Sphere (S m)) (Ptd-Wedge Z (Ptd-Susp X)))
            (SuspSmash.ptd-path (Ptd-Sphere m) X
             ∙ ptd-join-sphere X m)

  C-Sphere× : C n (Ptd-Sphere {i} m ×ptd X)
           == C n (Ptd-Sphere m) ×G (C n (Ptd-Susp^ m X) ×G C n X)
  C-Sphere× =
    ! (C-Susp n (Ptd-Sphere m ×ptd X))
    ∙ ap (C (succ n)) space-path
    ∙ C-binary-additive (succ n) (Ptd-Sphere (S m))
                                 (Ptd-Wedge (Ptd-Susp^ (S m) X) (Ptd-Susp X))
    ∙ ap (λ H → C (succ n) (Ptd-Sphere (S m)) ×G H)
         (C-binary-additive (succ n) (Ptd-Susp^ (S m) X) (Ptd-Susp X)
          ∙ ap2 _×G_ (C-Susp n (Ptd-Susp^ m X))
                     (C-Susp n X))
    ∙ ap (λ H → H ×G (C n (Ptd-Susp^ m X) ×G C n X))
         (C-Susp n (Ptd-Sphere m))
