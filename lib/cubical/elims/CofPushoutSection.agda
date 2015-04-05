{- OPTIONS --without -K #-}

open import HoTT
open import lib.cubical.elims.CubeMove

{- Given a span [A ←f– C –g→ B] and a map [h : A ⊔_C B → D] where
 - [g] has a left inverse:

 - To define a function [Cof(h) → E], one can give only the [cfbase], [cfcod],
 - [cfglue∘left], and [cfglue∘right] cases, and construct a map
 - which has the right behavior on [cfbase] and [cfcod].

 - In order to show that two maps [u v : Cof(h) → E] are equal,
 - it suffices to show that they agree on [cfbase], [cfcod],
 - [cfglue∘left], and [cfglue∘right].

 - This is useful for for proving equivalences where (at least) one side
 - involves one of these iterated pushouts. It could be generalized
 - further by loosening from Cof(h) to some more general class of pushouts,
 - but this is sufficient for the current applications. -}

module lib.cubical.elims.CofPushoutSection where

module _ {i j k l} {s : Span {i} {j} {k}} {D : Type l}
  (h : Pushout s → D) where

  open Span s

  module CofPushoutSection (r : B → C) (inv : ∀ c → r (g c) == c) where

    rec : ∀ {m} {E : Type m}
      (cfbase* : E) (cfcod* : D → E)
      (cfglue-left* : (a : A) → cfbase* == cfcod* (h (left a)))
      (cfglue-right* : (b : B) → cfbase* == cfcod* (h (right b)))
      → (Cofiber h → E)
    rec cfbase* cfcod* cfglue-left* cfglue-right* = CofiberRec.f _
      cfbase*
      cfcod*
      (Pushout-elim
        cfglue-left*
        (λ b → fst (fill (r b)) ∙ cfglue-right* b)
        (↓-cst=app-from-square ∘ λ c →
          transport
            (λ c' → Square (cfglue-left* (f c)) idp (ap (cfcod* ∘ h) (glue c))
                           (fst (fill c') ∙ cfglue-right* (g c)))
            (! (inv c))
            (snd (fill c))))
      where
      square-right-from-top : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
        {p : a₀₀ == a₀₁} {q : a₀₀ == a₁₀} {r : a₀₁ == a₁₁} {s : a₁₀ == a₁₁}
        → Square p q r s
        → Square p idp r (q ∙ s)
      square-right-from-top ids = ids

      fill : (c : C) →
        Σ (cfbase* == cfbase*)
          (λ p → Square (cfglue-left* (f c)) idp
                        (ap (cfcod* ∘ h) (glue c)) (p ∙ cfglue-right* (g c)))
      fill c = (fst fill' , square-right-from-top (snd fill'))
        where
        fill' = fill-square-top _ _ _

    path-elim : ∀ {m} {E : Type m} {u v : Cofiber h → E}
      (cfbase* : u (cfbase _) == v (cfbase _))
      (cfcod* : (d : D) → u (cfcod _ d) == v (cfcod _ d))
      (cfglue-left* : (a : A)
        → Square cfbase* (ap u (cfglue _ (left a)))
                 (ap v (cfglue _ (left a))) (cfcod* (h (left a))))
      (cfglue-right* : (b : B)
        → Square cfbase* (ap u (cfglue _ (right b)))
                 (ap v (cfglue _ (right b))) (cfcod* (h (right b))))
      → ∀ κ → u κ == v κ
    path-elim {u = u} {v = v} cfbase* cfcod* cfglue-left* cfglue-right* =
      Cofiber-elim _
        cfbase*
        cfcod*
        (↓-='-from-square ∘ Pushout-elim
          cfglue-left*
          (λ b → fst (fill (r b) (cfglue-right* (g (r b)))) ⊡h cfglue-right* b)
          (cube-to-↓-square ∘ λ c →
            transport
              (λ w → CubeType c (fst (fill w (cfglue-right* (g w)))
                                 ⊡h cfglue-right* (g c)))
              (! (inv c))
              (snd (fill _ _))))
      where
      SquareType : Pushout s → Type _
      SquareType γ =
        Square cfbase* (ap u (cfglue _ γ)) (ap v (cfglue _ γ)) (cfcod* (h γ))

      CubeType : (c : C) → SquareType (right (g c)) → Type _
      CubeType c sq =
        Cube (cfglue-left* (f c)) sq
          (natural-square (λ _ → cfbase*) (glue c))
          (natural-square (ap u ∘ cfglue _) (glue c))
          (natural-square (ap v ∘ cfglue _) (glue c))
          (natural-square (cfcod* ∘ h) (glue c))

      fill : (c : C) (sq : SquareType (right (g c)))
        → Σ (Square cfbase* idp idp cfbase*) (λ p → CubeType c (p ⊡h sq))
      fill c sq =
        (fst fill' , cube-right-from-front (fst fill') sq (snd fill'))
        where
        fill' = fill-cube-right _ _ _ _ _

    {- Note, only squares with constant endpoints. General case? -}
    square-elim : ∀ {m} {E : Type m} {e₀₀ e₀₁ e₁₀ e₁₁ : E}
      {p₀₋ : Cofiber h → e₀₀ == e₀₁} {p₋₀ : Cofiber h → e₀₀ == e₁₀}
      {p₋₁ : Cofiber h → e₀₁ == e₁₁} {p₁₋ : Cofiber h → e₁₀ == e₁₁}
      (base* : Square (p₀₋ (cfbase _)) (p₋₀ (cfbase _))
                      (p₋₁ (cfbase _)) (p₁₋ (cfbase _)))
      (cod* : (d : D) → Square (p₀₋ (cfcod _ d)) (p₋₀ (cfcod _ d))
                               (p₋₁ (cfcod _ d)) (p₁₋ (cfcod _ d)))
      → ((a : A) → Cube base* (cod* (h (left a)))
                     (natural-square p₀₋ (cfglue _ (left a)))
                     (natural-square p₋₀ (cfglue _ (left a)))
                     (natural-square p₋₁ (cfglue _ (left a)))
                     (natural-square p₁₋ (cfglue _ (left a))))
      → ((b : B) → Cube base* (cod* (h (right b)))
                     (natural-square p₀₋ (cfglue _ (right b)))
                     (natural-square p₋₀ (cfglue _ (right b)))
                     (natural-square p₋₁ (cfglue _ (right b)))
                     (natural-square p₁₋ (cfglue _ (right b))))
      → ((κ : Cofiber h) → Square (p₀₋ κ) (p₋₀ κ) (p₋₁ κ) (p₁₋ κ))
    square-elim base* cod* left* right* =
      disc-to-square ∘ path-elim
        (square-to-disc base*)
        (square-to-disc ∘ cod*)
        (cube-to-disc-square ∘ left*)
        (cube-to-disc-square ∘ right*)
