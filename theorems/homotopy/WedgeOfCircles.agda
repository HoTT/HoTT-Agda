{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module homotopy.WedgeOfCircles {i} where

WedgeOfCircles : (I : Type i) → Type i
WedgeOfCircles I = BigWedge {A = I} (λ _ → ⊙S¹)

