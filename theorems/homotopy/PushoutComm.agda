{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.PushoutComm where

-- How do I prevent [to] from being exported?
private
 module _ {i j k} (s : Span {i} {j} {k}) where

  open Span s

  flip : Span
  flip = span B A C g f

  to : Pushout s → Pushout flip
  to = To.f  module M where

    module To = PushoutRec right left (λ (c : C) → ! (glue c))

  open M public

private
 module _ {i j k} (s : Span {i} {j} {k}) where

  to-to-flip : (x : Pushout (flip s)) → to s (to (flip s) x) == x
  to-to-flip = Pushout-elim (λ _ → idp) (λ _ → idp)
    (λ c → ↓-∘=idf-in (to s) (to (flip s))
      (ap (to s) (ap (to (flip s)) (glue c))   =⟨ To.glue-β (flip s) c |in-ctx ap (to s) ⟩
       ap (to s) (! (glue c))                  =⟨ ap-! (to s) (glue c) ⟩
       ! (ap (to s) (glue c))                  =⟨ To.glue-β s c |in-ctx ! ⟩
       ! (! (glue c))                          =⟨ !-! (glue c) ⟩
       glue c ∎))

module _ {i j k} (s : Span {i} {j} {k}) where

  Pushout-comm : Pushout s ≃ Pushout (flip s)
  Pushout-comm = equiv (to s) (to (flip s)) (to-to-flip s) (to-to-flip (flip s))

