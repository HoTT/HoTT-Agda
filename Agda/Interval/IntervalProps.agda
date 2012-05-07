{-# OPTIONS --without-K #-}

open import Homotopy
open import Interval.Interval

module Interval.IntervalProps where

bool-split : bool → Set
bool-split true = unit
bool-split false = ⊥

bool-contr-path : is-contr bool → true ≡ false
bool-contr-path (x , f) = (f true) ∘ ! (f false)

bool-is-not-contractible : is-contr bool → ⊥
bool-is-not-contractible f = transport bool-split (bool-contr-path f) tt

interval-is-contractible : is-contr I
interval-is-contractible = (zero , (I-rec (λ (t : I) → t ≡ zero) (refl zero) (! seg) (trans-x≡a seg (refl zero) ∘ refl-right-unit (! seg))))

