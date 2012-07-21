{-# OPTIONS --without-K #-}

open import Base
open import Circle.Circle
open import Integers.Integers

module Circle.LoopSpace where

P-path : circle → Set _
P-path t = (t ≡ base)

tot-path : Set _
tot-path = Σ circle P-path

succ-path : ℤ ≡ ℤ
succ-path = eq-to-path succ-equiv

P-type : circle → Set _
P-type = circle-rec-nondep (Set _) ℤ succ-path

tot-type : Set _
tot-type = Σ circle P-type

tot-path-is-contr : is-contr tot-path
tot-path-is-contr = ((base , refl base) , pathto-is-contr)

trans-P-type : {u v : circle} (p : u ≡ v) (q : P-type u) → transport P-type p q ≡ transport (λ A → A) (map P-type p) q
trans-P-type (refl _) _ = refl _

loop-to-succ : (n : ℤ) → transport P-type loop n ≡ succ n
loop-to-succ n = trans-P-type loop n ∘ (map (λ t → transport (λ A → A) t n) (β-nondep Set ℤ succ-path) ∘ trans-eq-to-path succ-equiv n)

{-
Here is an HIT declaration for the CW-complex of real numbers:

data ℝ : Set where
  z : ℤ → ℝ
  e : (n : ℤ) → z n ≡ z (succ n)

It is not difficult to prove that ℝ is contractible.
We want to show that [tot-type] has the same introduction and elimination rules, so that we can prove that [tot-type] is contractible too.
-}

-- Introduction rules
R-z : ℤ → tot-type
R-z n = (base , n)

R-e : (n : ℤ) → R-z n ≡ R-z (succ n)
R-e n = total-path loop (loop-to-succ n)

-- Elimination rule
module Tot-type-is-ℝ
  {i}
  (P : tot-type → Set i)
  (z : (n : ℤ) → P (R-z n))
  (e : (n : ℤ) → transport P (R-e n) (z n) ≡ z (succ n)) where

  -- I redefine [R-e] and [e] to have something involving [transport P-type loop] instead of [succ]
  R-e' : (n : ℤ) → R-z n ≡ R-z (transport P-type loop n)
  R-e' n = total-path loop (refl _)

  e' : (n : ℤ) → transport P (R-e' n) (z n) ≡ z (transport P-type loop n)
  e' n = (trans-totalpath {P = P-type} {Q = P} {x = (base , n)} {y = (base , transport P-type loop n)} loop (refl _) z
         ∘ move!-transp-left (λ z → P (base , z)) _ (loop-to-succ n) (z (succ n))
           (! (trans-totalpath {P = P-type} {Q = P} {x = (base , n)} {y = (base , succ n)} loop (loop-to-succ n) z)
            ∘ e n))
          ∘ map-dep z (! (loop-to-succ n))

  -- Now I can prove what I want by induction on the circle

  P-base : (t : P-type base) → P (base , t)
  P-base t = z t

  P-loop : (t : P-type base) → transport (λ x → (u : P-type x) → P (x , u)) loop P-base t ≡ P-base t
  P-loop t = transport (λ t → transport (λ x → (u : P-type x) → P (x , u)) loop P-base t ≡ P-base t) (trans-trans-opposite {P = P-type} loop t)
               (! (trans-totalpath {P = P-type} {Q = P} loop (refl _) z)
               ∘ e' (transport P-type (! loop) t))

  P-R-rec : (x : circle) → (t : P-type x) → P (x , t)
  P-R-rec = circle-rec (λ x → (t : P-type x) → P (x , t)) P-base (funext-dep P-loop)

  -- Here is the conclusion of the elimination rule
  R-rec : (t : tot-type) → P t
  R-rec (x , y) = P-R-rec x y

-- We can now prove that [tot-type] is contractible using [R-rec], that’s a little tedious but not difficult
P-R-contr : (x : tot-type) → Set _
P-R-contr x = R-z O ≡ x

R-contr-base : (n : ℤ) → P-R-contr (R-z n)
R-contr-base O = refl _
R-contr-base (pos O) = R-e O
R-contr-base (pos (S y)) = R-contr-base (pos y) ∘ R-e (pos y)
R-contr-base (neg O) = ! (R-e (neg O))
R-contr-base (neg (S y)) = R-contr-base (neg y) ∘ ! (R-e (neg (S y)))

R-contr-loop : (n : ℤ) → transport P-R-contr (R-e n) (R-contr-base n) ≡ (R-contr-base (succ n))
R-contr-loop O = trans-a≡x (R-e O) (refl _)
R-contr-loop (pos O) = trans-a≡x (R-e (pos O)) (R-e O)
R-contr-loop (pos (S y)) = trans-a≡x (R-e (pos (S y))) (R-contr-base (pos y) ∘ R-e (pos y))
R-contr-loop (neg O) = trans-a≡x (R-e (neg O)) (! (R-e (neg O))) ∘ opposite-left-inverse (R-e (neg O))
R-contr-loop (neg (S y)) =
  ((trans-a≡x (R-e (neg (S y))) (R-contr-base (neg y) ∘ ! (R-e (neg (S y))))
   ∘ concat-assoc (R-contr-base (neg y)) (! (R-e (neg (S y)))) (R-e (neg (S y))))
   ∘ (whisker-left (R-contr-base (neg y)) (opposite-left-inverse (R-e (neg (S y))))))
   ∘ refl-right-unit (R-contr-base (neg y))

R-contr : (x : tot-type) → P-R-contr x
R-contr = Tot-type-is-ℝ.R-rec P-R-contr R-contr-base R-contr-loop

tot-type-is-contr : is-contr tot-type
tot-type-is-contr = (R-z O , λ x → ! (R-contr x))

-- We define now a fiberwise map between the two fibrations [P-path] and [P-type]
fiberwise-map : (x : circle) → (P-path x → P-type x)
fiberwise-map x p = transport P-type (! p) O

-- This induces an equivalence on the total spaces, because both total spaces are contractible
total-is-equiv : is-equiv (total-map fiberwise-map)
total-is-equiv = contr-equiv-contr (total-map fiberwise-map) tot-path-is-contr tot-type-is-contr

-- Hence an equivalence fiberwise
fibers-equiv : (x : circle) → is-equiv (fiberwise-map x)
fibers-equiv x = fiberwise-equiv fiberwise-map total-is-equiv x

-- We can then conclude that the based loop space of the circle is equivalent to the type of
-- the integers
ΩS¹≃ℤ : (base ≡ base) ≃ ℤ
ΩS¹≃ℤ = (fiberwise-map base , fibers-equiv base)

-- We can also deduce that the circle is of h-level 3

ΩS¹-is-set : is-set (base ≡ base)
ΩS¹-is-set = equiv-types-hlevel 2 (ΩS¹≃ℤ ⁻¹) ℤ-is-set

circle-is-gpd : is-gpd circle
circle-is-gpd =
  circle-rec _
    (circle-rec _
      ΩS¹-is-set  -- [base ≡ base] is a set
      (π₁ (is-hlevel-is-prop 2 _ _ _)))
    (funext-dep (circle-rec _
                  (π₁ (is-hlevel-is-prop 2 _ _ _))
                  (π₁ (is-increasing-hlevel 1 _ (is-hlevel-is-prop 2 _) _ _ _ _))))
