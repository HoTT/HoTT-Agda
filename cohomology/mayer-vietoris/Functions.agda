{-# OPTIONS --without-K #-}

open import HoTT

module cohomology.mayer-vietoris.Functions
  {i j k} (ps : Ptd-Span {i} {j} {k}) where

  open Ptd-Span ps


  module Reglue = WedgeRec
    {X = Ptd-Span.X ps} {Y = Ptd-Span.Y ps} {C = fst (Ptd-Pushout ps)}
    left right (! (ap left (snd f)) ∙ glue (snd Z) ∙' ap right (snd g))

  reglue : Wedge X Y → fst (Ptd-Pushout ps)
  reglue = Reglue.f

  ptd-reglue : fst (Ptd-Wedge X Y ∙→ Ptd-Pushout ps)
  ptd-reglue = (reglue , idp)


  module ExtractGlue = PushoutRec {d = ptd-span-out ps} {D = Suspension (fst Z)}
    (λ _ → north _) (λ _ → south _) (merid _)

  extract-glue = ExtractGlue.f

  ptd-extract-glue : fst (Ptd-Pushout ps ∙→ Ptd-Susp Z)
  ptd-extract-glue = (extract-glue , idp)

