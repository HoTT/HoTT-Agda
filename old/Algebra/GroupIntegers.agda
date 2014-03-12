{-# OPTIONS --without-K #-}

open import Base
open import Algebra.Groups
open import Integers

module Algebra.GroupIntegers where

_+_ : ℤ → ℤ → ℤ
O + m = m
pos O + m = succ m
pos (S n) + m = succ (pos n + m)
neg O + m = pred m
neg (S n) + m = pred (neg n + m)

-_ : ℤ → ℤ
- O = O
- (pos m) = neg m
- (neg m) = pos m

+-succ : (m n : ℤ) → succ m + n ≡ succ (m + n)
+-succ O n = refl _
+-succ (pos m) n = refl _
+-succ (neg O) n = ! (succ-pred n)
+-succ (neg (S m)) n = ! (succ-pred _)

+-pred : (m n : ℤ) → pred m + n ≡ pred (m + n)
+-pred O n = refl _
+-pred (pos O) n = ! (pred-succ n)
+-pred (pos (S m)) n = ! (pred-succ _)
+-pred (neg m) n = refl _

+-assoc : (m n p : ℤ) → (m + n) + p ≡ m + (n + p)
+-assoc O n p = refl _
+-assoc (pos O) n p = +-succ n p
+-assoc (pos (S m)) n p = +-succ (pos m + n) p ∘ map succ (+-assoc (pos m) n p)
+-assoc (neg O) n p = +-pred n p
+-assoc (neg (S m)) n p = +-pred (neg m + n) p ∘ map pred (+-assoc (neg m) n p)

O-right-unit : (m : ℤ) → m + O ≡ m
O-right-unit O = refl _
O-right-unit (pos O) = refl _
O-right-unit (pos (S m)) = map succ (O-right-unit (pos m))
O-right-unit (neg O) = refl _
O-right-unit (neg (S m)) = map pred (O-right-unit (neg m))

succ-+-right : (m n : ℤ) → succ (m + n) ≡ m + succ n
succ-+-right O n = refl _
succ-+-right (pos O) n = refl _
succ-+-right (pos (S m)) n = map succ (succ-+-right (pos m) n)
succ-+-right (neg O) n = succ-pred n ∘ ! (pred-succ n)
succ-+-right (neg (S m)) n = (succ-pred (neg m + n) ∘ ! (pred-succ (neg m + n)))
                             ∘ map pred (succ-+-right (neg m) n)

pred-+-right : (m n : ℤ) → pred (m + n) ≡ m + pred n
pred-+-right O n = refl _
pred-+-right (pos O) n = pred-succ n ∘ ! (succ-pred n)
pred-+-right (pos (S m)) n = (pred-succ (pos m + n) ∘ ! (succ-pred (pos m + n)))
                             ∘ map succ (pred-+-right (pos m) n)
pred-+-right (neg O) n = refl _
pred-+-right (neg (S m)) n = map pred (pred-+-right (neg m) n)

opp-right-inverse : (m : ℤ) → m + (- m) ≡ O
opp-right-inverse O = refl O
opp-right-inverse (pos O) = refl O
opp-right-inverse (pos (S m)) = succ-+-right (pos m) (neg (S m))
                                ∘ opp-right-inverse (pos m)
opp-right-inverse (neg O) = refl O
opp-right-inverse (neg (S m)) = pred-+-right (neg m) (pos (S m))
                                ∘ opp-right-inverse (neg m)

opp-left-inverse : (m : ℤ) → (- m) + m ≡ O
opp-left-inverse O = refl O
opp-left-inverse (pos O) = refl O
opp-left-inverse (pos (S m)) = pred-+-right (neg m) (pos (S m))
                               ∘ opp-left-inverse (pos m)
opp-left-inverse (neg O) = refl O
opp-left-inverse (neg (S m)) = succ-+-right (pos m) (neg (S m))
                               ∘ opp-left-inverse (neg m)
                 -- pred-+-right (neg m) (pos (S m)) ∘ opp-left-inverse (pos m)

ℤ-group : Group _
ℤ-group = group (pregroup
  ℤ
  _+_ O -_
  +-assoc O-right-unit (λ m → refl _) opp-right-inverse opp-left-inverse)
  ℤ-is-set
