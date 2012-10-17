{-# OPTIONS --without-K #-}

open import Base
open import Spaces.Interval

module Spaces.IntervalProps where

bool-split : bool → Set
bool-split true = unit
bool-split false = ⊥

-- If [bool] is contractible, then [true ≡ false]
bool-contr-path : is-contr bool → true ≡ false
bool-contr-path (x , f) = (f true) ∘ ! (f false)

-- But if [true ≡ false], then [⊥]
bool-is-not-contr : ¬ (is-contr bool)
bool-is-not-contr f = transport bool-split (bool-contr-path f) tt

I-is-contr : is-contr I
I-is-contr =
  (zer , I-rec (λ (t : I) → t ≡ zer) (refl zer) (! seg)
                (trans-x≡a seg (refl zer) ∘ refl-right-unit (! seg)))

interval-implies-funext : ∀ {i j} (A : Set i) (B : Set j) (f g : A → B)
  (h : (x : A) → f x ≡ g x) → f ≡ g
interval-implies-funext A B f g h =
  map (λ i a → I-rec-nondep _ (f a) (g a) (h a) i) seg
