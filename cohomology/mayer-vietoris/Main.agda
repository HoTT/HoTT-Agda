{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.CofiberSequence
open import cohomology.mayer-vietoris.BaseEquivalence
  using (base-equiv; base-ptd-path)
open import cohomology.mayer-vietoris.BaseFunctionsOver
  using (base-cfcod-over)

module cohomology.mayer-vietoris.Main {i} where

open import cohomology.mayer-vietoris.Functions public

module _ (ps : Ptd-Span {i} {i} {i}) where

  open Ptd-Span ps

  {- We use path induction (via [ptd-pushout-J]) to assume that the
     basepoint preservation paths of the span maps are [idp]. The
     proofs for that case are in [BaseEquivalence] and [BaseFunctionsOver].
   -}

  mv-equiv : Cofiber (reglue ps) ≃ Suspension (fst Z)
  mv-equiv = ptd-pushout-J
    (λ ps' → Cofiber (reglue ps') ≃ Suspension (fst (Ptd-Span.Z ps')))
    base-equiv ps

  mv-path : Cofiber (reglue ps) == Suspension (fst Z)
  mv-path = ua mv-equiv

  mv-ptd-path : Ptd-Cof (ptd-reglue ps) == Ptd-Susp Z
  mv-ptd-path = ptd-pushout-J
    (λ ps' → Ptd-Cof (ptd-reglue ps') == Ptd-Susp (Ptd-Span.Z ps'))
    base-ptd-path ps

module _ (ps : Ptd-Span {i} {i} {i}) where

  open Ptd-Span ps

  mv-cfcod-over : ptd-cfcod (ptd-reglue ps) == ptd-extract-glue ps
    [ (λ W → fst (Ptd-Pushout ps ∙→ W)) ↓ mv-ptd-path ps ]
  mv-cfcod-over = ptd-pushout-J
    (λ ps' → ptd-cfcod (ptd-reglue ps') == ptd-extract-glue ps'
      [ (λ W → fst (Ptd-Pushout ps' ∙→ W)) ↓ mv-ptd-path ps' ])
    base-cfcod-over ps
