{-# OPTIONS --without-K #-}

open import Base
open import Spaces.Circle
open import Integers

module Spaces.LoopSpaceCircle where

-- Path fibration

path-fib : S¹ → Set
path-fib t = (t ≡ base)

tot-path-fib : Set
tot-path-fib = Σ S¹ path-fib

tot-path-fib-is-contr : is-contr tot-path-fib
tot-path-fib-is-contr = pathto-is-contr base

-- Universal cover

succ-path : ℤ ≡ ℤ
succ-path = eq-to-path succ-equiv

universal-cover : S¹ → Set
universal-cover = S¹-rec-nondep Set ℤ succ-path

tot-cover : Set
tot-cover = Σ S¹ universal-cover

-- Transport in the universal cover
loop-to-succ : (n : ℤ) → transport universal-cover loop n ≡ succ n
loop-to-succ n = ! (trans-ap (λ A → A) universal-cover loop n)
                 ∘ (ap (λ t → transport (λ A → A) t n)
                        (S¹-β-loop-nondep Set ℤ succ-path)
                 ∘ trans-id-eq-to-path succ-equiv n)

{- The flattening lemma

Here is an HIT declaration for the CW-complex of real numbers:

data ℝ : Set where
  z : ℤ → ℝ
  e : (n : ℤ) → z n ≡ z (succ n)

We want to show that [tot-cover] has the same introduction and elimination
rules.
-}

-- Introduction rules

R-z : ℤ → tot-cover
R-z n = (base , n)

R-e : (n : ℤ) → R-z n ≡ R-z (succ n)
R-e n = Σ-eq loop (loop-to-succ n)

-- Elimination rule
module Tot-cover-is-ℝ
  {i}
  (P : tot-cover → Set i)
  (z : (n : ℤ) → P (R-z n))
  (e : (n : ℤ) → transport P (R-e n) (z n) ≡ z (succ n)) where

  -- I redefine [R-e] and [e] to have something involving
  -- [transport universal-cover loop] instead of [succ]
  R-e' : (n : ℤ) → R-z n ≡ R-z (transport universal-cover loop n)
  R-e' n = Σ-eq loop refl

  e' : (n : ℤ) → transport P (R-e' n) (z n)
                 ≡ z (transport universal-cover loop n)
  e' n = (trans-totalpath universal-cover P {x = (base , n)}
                          {y = (base , transport universal-cover loop n)}
                          loop refl z
         ∘ move!-transp-left (λ z → P (base , z)) _ (loop-to-succ n)
           (z (succ n))
           (! (trans-totalpath universal-cover P {x = (base , n)}
                               {y = (base , succ n)} loop (loop-to-succ n) z)
            ∘ e n))
          ∘ apd z (! (loop-to-succ n))

  -- Now I can prove what I want by induction on the circle

  P-base : (t : universal-cover base) → P (base , t)
  P-base t = z t

  P-loop : (t : universal-cover base)
    → transport (λ x → (u : universal-cover x) → P (x , u)) loop P-base t
      ≡ P-base t
  P-loop t = transport (λ t → transport
                                (λ x → (u : universal-cover x) → P (x , u))
                                loop P-base t ≡ P-base t)
               (trans-trans-opposite universal-cover loop t)
               (! (trans-totalpath universal-cover P
                                   loop refl z)
               ∘ e' (transport universal-cover (! loop) t))

  P-R-rec : (x : S¹) → (t : universal-cover x) → P (x , t)
  P-R-rec = S¹-rec (λ x → (t : universal-cover x) → P (x , t))
                   P-base (funext P-loop)

  -- Here is the conclusion of the elimination rule
  R-rec : (t : tot-cover) → P t
  R-rec (x , y) = P-R-rec x y

-- We can now prove that [tot-cover] is contractible using [R-rec], that’s a
-- little tedious but not difficult

P-R-contr : (x : tot-cover) → Set _
P-R-contr x = R-z O ≡ x

R-contr-base : (n : ℤ) → P-R-contr (R-z n)
R-contr-base O = refl
R-contr-base (pos O) = R-e O
R-contr-base (pos (S y)) = R-contr-base (pos y) ∘ R-e (pos y)
R-contr-base (neg O) = ! (R-e (neg O))
R-contr-base (neg (S y)) = R-contr-base (neg y) ∘ ! (R-e (neg (S y)))

R-contr-loop : (n : ℤ)
  → transport P-R-contr (R-e n) (R-contr-base n) ≡ (R-contr-base (succ n))
R-contr-loop O = trans-cst≡id (R-e O) refl
R-contr-loop (pos O) = trans-cst≡id (R-e (pos O)) (R-e O)
R-contr-loop (pos (S y)) = trans-cst≡id (R-e (pos (S y)))
  (R-contr-base (pos y) ∘ R-e (pos y))
R-contr-loop (neg O) = trans-cst≡id (R-e (neg O))
  (! (R-e (neg O))) ∘ opposite-left-inverse (R-e (neg O))
R-contr-loop (neg (S y)) =
  ((trans-cst≡id (R-e (neg (S y))) (R-contr-base (neg y) ∘ ! (R-e (neg (S y))))
   ∘ concat-assoc (R-contr-base (neg y)) (! (R-e (neg (S y))))
                  (R-e (neg (S y))))
   ∘ (whisker-left (R-contr-base (neg y))
                   (opposite-left-inverse (R-e (neg (S y))))))
   ∘ refl-right-unit (R-contr-base (neg y))

R-contr : (x : tot-cover) → P-R-contr x
R-contr = Tot-cover-is-ℝ.R-rec P-R-contr R-contr-base R-contr-loop

tot-cover-is-contr : is-contr tot-cover
tot-cover-is-contr = (R-z O , λ x → ! (R-contr x))

-- We define now a fiberwise map between the two fibrations [path-fib]
-- and [universal-cover]
fiberwise-map : (x : S¹) → (path-fib x → universal-cover x)
fiberwise-map x p = transport universal-cover (! p) O

-- This induces an equivalence on the total spaces, because both total spaces
-- are contractible
total-is-equiv : is-equiv (total-map fiberwise-map)
total-is-equiv = contr-to-contr-is-equiv (total-map fiberwise-map)
                                         tot-path-fib-is-contr
                                         tot-cover-is-contr

-- Hence an equivalence fiberwise
fiberwise-map-is-equiv : (x : S¹) → is-equiv (fiberwise-map x)
fiberwise-map-is-equiv x = fiberwise-is-equiv fiberwise-map total-is-equiv x

-- We can then conclude that the based loop space of the circle is equivalent to
-- the type of the integers
ΩS¹≃ℤ : (base ≡ base) ≃ ℤ
ΩS¹≃ℤ = (fiberwise-map base , fiberwise-map-is-equiv base)

-- We can also deduce that the circle is 1-truncated

ΩS¹-is-set : is-set (base ≡ base)
ΩS¹-is-set = equiv-types-truncated _ (ΩS¹≃ℤ ⁻¹) ℤ-is-set

S¹-is-gpd : is-gpd S¹
S¹-is-gpd =
  S¹-rec _
    (S¹-rec _
      ΩS¹-is-set  -- [base ≡ base] is a set
      (π₁ (is-truncated-is-prop _ _ _)))
    (funext
      (S¹-rec _
        (π₁ (is-truncated-is-prop _ _ _))
        (prop-has-all-paths (≡-is-truncated _ (is-truncated-is-prop _)) _ _)))
