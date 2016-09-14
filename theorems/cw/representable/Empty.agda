{-# OPTIONS --without-K #-}

open import HoTT
open import cw.CW

module cw.representable.Empty where

cw-empty-skel : Skeleton {lzero} 0
cw-empty-skel = skel-base (Empty , Empty-is-set)
CWEmpty = ⟦ cw-empty-skel ⟧

CWEmpty-equiv-Empty : CWEmpty ≃ Empty
CWEmpty-equiv-Empty = ide _

