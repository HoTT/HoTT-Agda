{-# OPTIONS --without-K #-}

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
  (h : Pushout s → D) where

  open Span s

  module CofPushoutSection (r : B → C) (inv : ∀ c → r (g c) == c) where

    elim : ∀ {m} {P : Cofiber h → Type m}
      (cfbase* : P (cfbase _)) (cfcod* : (d : D) → P (cfcod _ d))
      (cfglue-left* : (a : A) →
        cfbase* == cfcod* (h (left a)) [ P ↓ cfglue _ (left a) ])
      (cfglue-right* : (b : B) →
        cfbase* == cfcod* (h (right b)) [ P ↓ cfglue _ (right b) ])
      → Π (Cofiber h) P
    elim {P = P} cfbase* cfcod* cfglue-left* cfglue-right* =
      Cofiber-elim _
        cfbase*
        cfcod*
        (Pushout-elim
          cfglue-left*
          (λ b → (fst (fill (r b))) ◃ cfglue-right* b)
          (λ c →
            transport
              (λ c' → cfglue-left* (f c) == fst (fill c') ◃ cfglue-right* (g c)
                      [ (λ γ → cfbase* == cfcod* (h γ) [ P ↓ cfglue _ γ ])
                        ↓ glue c ])
              (! (inv c))
              (snd (fill c))))
      where
      fill : (c : C)
        → Σ (cfbase* == cfbase*)
            (λ q → cfglue-left* (f c) == (q ◃ (cfglue-right* (g c)))
                   [ (λ γ → cfbase* == cfcod* (h γ) [ P ↓ cfglue _ γ ])
                     ↓ glue c ])
      fill c =
        ↓↓-fill (glue c) (cfglue-left* (f c)) (cfglue-right* (g c))

    rec : ∀ {m} {E : Type m}
      (cfbase* : E) (cfcod* : D → E)
      (cfglue-left* : (a : A) → cfbase* == cfcod* (h (left a)))
      (cfglue-right* : (b : B) → cfbase* == cfcod* (h (right b)))
      → (Cofiber h → E)
    rec cfbase* cfcod* cfglue-left* cfglue-right* =
      elim cfbase* cfcod* (↓-cst-in ∘ cfglue-left*) (↓-cst-in ∘ cfglue-right*)
