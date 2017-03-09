{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Truncation
open import lib.types.Groupoid
open import lib.types.PathSet

module lib.groupoids.FundamentalPreGroupoid {i} (A : Type i) where

  fundamental-pregroupoid : PreGroupoid i i
  fundamental-pregroupoid = record
    { El = A
    ; Arr = _=₀_ {A = A}
    ; Arr-level = λ _ _ → Trunc-level
    ; groupoid-struct = record
      { ident = idp₀
      ; inv = !₀
      ; comp = _∙₀_
      ; unit-l = ∙₀-unit-l
      ; assoc = ∙₀-assoc
      ; inv-l = !₀-inv-l
      }
    }
