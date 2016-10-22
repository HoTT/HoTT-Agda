{-# OPTIONS --without-K #-}

open import HoTT
open import cw.CW

module cw.examples.Empty where

cw-empty-skel : Skeleton {lzero} 0
cw-empty-skel = Empty , Empty-is-set
CWEmpty = ⟦ cw-empty-skel ⟧

CWEmpty-equiv-Empty : CWEmpty ≃ Empty
CWEmpty-equiv-Empty = ide _

