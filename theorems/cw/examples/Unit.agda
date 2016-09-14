{-# OPTIONS --without-K #-}

open import HoTT
open import cw.CW

module cw.examples.Unit where

cw-unit-skel : Skeleton {lzero} 0
cw-unit-skel = skel-base (Unit , Unit-is-set)
CWUnit = ⟦ cw-unit-skel ⟧

CWUnit-equiv-Unit : CWUnit ≃ Unit
CWUnit-equiv-Unit = ide _
