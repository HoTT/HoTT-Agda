{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Truncation
open import lib.types.Groupoid
open import lib.types.PathSet

module lib.types.FundamentalGroupoid {i} (A : Type i) where

  fundamental-groupoid : Groupoid
  fundamental-groupoid = record
    { El = A
    ; Arr = _=₀_ {A = A}
    ; Arr-level = λ _ _ → Trunc-level
    ; groupoid-struct = record
      { id = idp₀
      ; inv = !₀
      ; comp = _∙₀_
      ; unit-l = ∙₀-unit-l
      ; unit-r = ∙₀-unit-r
      ; assoc = ∙₀-assoc
      ; inv-l = !₀-inv-l
      ; inv-r = !₀-inv-r
      }
    }
