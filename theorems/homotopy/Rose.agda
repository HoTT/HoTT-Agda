{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.Rose {i} where

Rose : (I : Type i) → Type i
Rose I = BigWedge {A = I} (λ _ → ⊙S¹)
