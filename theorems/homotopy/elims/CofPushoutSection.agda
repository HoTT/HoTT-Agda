{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.elims.Lemmas

{- Given a span [A ←f– C –g→ B] and a map [h : A ⊔_C B → D] where
 - [g] has a left inverse:

 - To define a fundction  [Π (Cof h) P], one can give only the [cfbase],
 - [cfcod], [cfglue∘left], and [cfglue∘right] cases, and construct a map
 - which has the right behavior on [cfbase], [cfcod], [cfglue∘left],
 - with [cfglue∘right] edited to achieve the highest coherence.

 - This is useful for for proving equivalences where (at least) one side
 - involves one of these iterated pushouts. It could be generalized
 - further by loosening from cofiber to some more general class of pushouts,
 - but this is sufficient for the current applications. -}

module homotopy.elims.CofPushoutSection where

module _ {i j k l} {s : Span {i} {j} {k}} {D : Type l}
  {h : Pushout s → D} where

  open Span s

  module CofPushoutSection (r : B → C) (inv : ∀ c → r (g c) == c) where

    elim : ∀ {m} {P : Cofiber h → Type m}
      (cfbase* : P cfbase) (cfcod* : (d : D) → P (cfcod d))
      (cfglue-left* : (a : A) →
        cfbase* == cfcod* (h (left a)) [ P ↓ cfglue (left a) ])
      (cfglue-right* : (b : B) →
        cfbase* == cfcod* (h (right b)) [ P ↓ cfglue (right b) ])
      → Π (Cofiber h) P
    elim {P = P} cfbase* cfcod* cfglue-left* cfglue-right* =
      Cofiber-elim
        cfbase*
        cfcod*
        (Pushout-elim
          cfglue-left*
          (λ b → (fst (fill (r b))) ◃ cfglue-right* b)
          (λ c → ↓↓-from-squareover $
            transport
              (λ c' → SquareOver P (natural-square cfglue (glue c))
                  (cfglue-left* (f c))
                  (↓-ap-in P (λ _ → cfbase) (apd (λ _ → cfbase*) (glue c)))
                  (↓-ap-in P (cfcod ∘ h) (apd (cfcod* ∘ h) (glue c)))
                  (fst (fill c') ◃ cfglue-right* (g c)))
              (! (inv c))
              (snd (fill c))))
      where
      fill : (c : C)
        → Σ (cfbase* == cfbase*)
            (λ q → SquareOver P (natural-square cfglue (glue c))
                     (cfglue-left* (f c)) _ _ (q ◃ cfglue-right* (g c)))
      fill c = fill-upper-right _ _ _ _ _


    rec : ∀ {m} {E : Type m}
      (cfbase* : E) (cfcod* : D → E)
      (cfglue-left* : (a : A) → cfbase* == cfcod* (h (left a)))
      (cfglue-right* : (b : B) → cfbase* == cfcod* (h (right b)))
      → (Cofiber h → E)
    rec cfbase* cfcod* cfglue-left* cfglue-right* =
      elim cfbase* cfcod* (↓-cst-in ∘ cfglue-left*) (↓-cst-in ∘ cfglue-right*)
