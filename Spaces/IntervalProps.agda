{-# OPTIONS --without-K #-}

open import Base
open import Spaces.Interval

module Spaces.IntervalProps where

bool-split : bool → Set
bool-split true = unit
bool-split false = ⊥ {zero-u}

-- If [bool] is contractible, then [true ≡ false]
bool-contr-path : is-contr bool → true ≡ false
bool-contr-path (x , f) = (f true) ∘ ! (f false)

-- But if [true ≡ false], then [⊥]
bool-is-not-contractible : is-contr bool → ⊥ {zero-u}
bool-is-not-contractible f = transport bool-split (bool-contr-path f) tt

interval-is-contractible : is-contr I
interval-is-contractible =
  (zero , I-rec (λ (t : I) → t ≡ zero) (refl zero) (! seg)
                (trans-x≡a seg (refl zero) ∘ refl-right-unit (! seg)))

interval-funext : ∀ {i j} (A : Set i) (B : Set j) (f g : A → B)
  (h : (x : A) → f x ≡ g x) → f ≡ g
interval-funext A B f g h = map (λ i a → I-rec-nondep _ (f a) (g a) (h a) i) seg
