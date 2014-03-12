{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.S1SuspensionS0 where

{- To -}

module To = S¹Rec (north Bool) (merid _ false ∙ ! (merid _ true))

to : S¹ → Suspension Bool
to = To.f

{- From -}

from-merid : Bool → base == base
from-merid true = loop
from-merid false = idp

module From = SuspensionRec Bool base base from-merid

from : Suspension Bool → S¹
from = From.f

{- ToFrom and FromTo -}

postulate  -- TODO, easy and boring
  to-from : (x : Suspension Bool) → to (from x) == x
  from-to : (x : S¹) → from (to x) == x

e : S¹ ≃ Suspension Bool
e = equiv to from to-from from-to
