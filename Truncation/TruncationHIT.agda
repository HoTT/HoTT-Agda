{-# OPTIONS --without-K #-}

open import Base
open import Truncation.TruncatedHIT

{-

The idea of the truncation is that it’s defined by the following HIT:

data τ n A : Set where
  proj : A → τ n A

  top  : (f : Sⁿ n → τ n A) → τ n A
  rays : (f : Sⁿ n → τ n A) (x : Sⁿ n) → top f ≡ f x

But there is an issue that the previous definition does not work for [n = 0],
because this gives [A] plus a point instead of giving a contractible space. And
I cannot define the 0th truncation separately because I want the elimination
rule to compute on [proj].

Hence I’m adding the following path constructor

  hack-prop : (p : n ≡ 0) (x y : τ) → (x ≡ y)

This will force [τ 0 A] to be contractible and does not change anything when [n]
is not 0.

-}

module Truncation.TruncationHIT {i} (n : ℕ) (A : Set i) where

private
  data #τ : Set i where
    #proj : A → #τ

    #top : (f : Sⁿ n → #τ) → #τ

τ : Set i
τ = #τ

proj : A → τ
proj = #proj

top : (f : Sⁿ n → τ) → τ
top = #top

postulate  -- HIT
  rays : (f : Sⁿ n → τ) (x : Sⁿ n) → top f ≡ f x
  hack-prop : (p : n ≡ 0) (x y : τ) → (x ≡ y)

#τ-rec : ∀ {j} (P : τ → Set j)
  (proj* : (x : A) → P (proj x))
  (top* : (f : Sⁿ n → τ) (p : (x : Sⁿ n) → P (f x)) → P (top f))
  (rays* : (f : Sⁿ n → τ) (p : (x : Sⁿ n) → P (f x)) (x : Sⁿ n)
    → transport P (rays f x) (top* f p) ≡ p x)
  (hack-prop* : (p : n ≡ 0) (x y : τ) (x* : P x) (y* : P y)
    → (transport P (hack-prop p x y) x* ≡ y* ))
  → ((x : τ) → P x)
#τ-rec P proj* top* rays* hack-prop* (#proj u) = proj* u
#τ-rec P proj* top* rays* hack-prop* (#top f) =
  top* f (λ x → #τ-rec P proj* top* rays* hack-prop* (f x))

#τ-rec-nondep : ∀ {j} (C : Set j)
  (proj* : A → C)
  (top* : (f : Sⁿ n → τ) (p : Sⁿ n → C) → C)
  (rays* : (f : Sⁿ n → τ) (p : Sⁿ n → C) (x : Sⁿ n) → top* f p ≡ p x)
  (hack-prop* : (p : n ≡ 0) (x y : τ) (x* y* : C) → x* ≡ y* )
  → (τ → C)
#τ-rec-nondep C proj* top* rays* hack-prop* (#proj u) = proj* u
#τ-rec-nondep C proj* top* rays* hack-prop* (#top f) =
  top* f (λ x → #τ-rec-nondep C proj* top* rays* hack-prop* (f x))

private
  contr : (n ≡ 0) → is-contr τ
  contr p = inhab-prop-is-contr τ (all-paths-is-prop (hack-prop p))
                                  (top (λ x → abort-nondep (transport Sⁿ p x)))

-- Computation rules for [rays] are not needed

τ-rec :  ∀ {j} (P : τ → Set j)
  (proj* : (x : A) → P (proj x))
  (hack-prop* : (p : n ≡ 0) (x y : τ) (x* : P x) (y* : P y)
    → (transport P (hack-prop p x y) x* ≡ y* ))
  (trunc : (x : τ) → is-hlevel n (P x))
  → ((x : τ) → P x)
τ-rec P proj* hack-prop* trunc =
  #τ-rec P proj* (λ f p₁ → π₁ (u f p₁))
                 (λ f p₁ → π₂ (u f p₁)) hack-prop* where
  u : _
  u = hlevel-n-has-filling-dep τ P n contr (λ f → (top f , rays f))

τ-rec-nondep : ∀ {j} (C : Set j)
  (proj* : A → C)
  (hack-prop* : (p : n ≡ 0) (x y : τ) (x* y* : C) → x* ≡ y* )
  (trunc : is-hlevel n C)
  → (τ → C)
τ-rec-nondep C proj* hack-prop* trunc =
  #τ-rec-nondep C proj* (λ _ p → π₁ (u p))
                        (λ _ p → π₂ (u p)) hack-prop* where
  u : _
  u = hlevel-n-has-n-spheres-filled n _ trunc

-- The nth truncation is of h-level [n]
abstract
  τ-hlevel : is-hlevel n τ
  τ-hlevel = n-spheres-filled-hlevel n τ contr (λ f → (top f , rays f))
