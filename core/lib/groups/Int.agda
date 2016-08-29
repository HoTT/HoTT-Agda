{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Int
open import lib.types.Group

module lib.groups.Int where

ℤ-group-structure : GroupStructure ℤ
ℤ-group-structure = record
  { ident = 0
  ; inv = ℤ~
  ; comp = _ℤ+_
  ; unit-l = ℤ+-unit-l
  ; unit-r = ℤ+-unit-r
  ; assoc = ℤ+-assoc
  ; inv-r = ℤ~-inv-r
  ; inv-l = ℤ~-inv-l
  }

ℤ-group : Group₀
ℤ-group = group _ ℤ-is-set ℤ-group-structure
