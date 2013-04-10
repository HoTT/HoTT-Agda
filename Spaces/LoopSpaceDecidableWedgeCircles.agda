{-# OPTIONS --without-K #-}

open import Base

module Spaces.LoopSpaceDecidableWedgeCircles {i} (A : Set i) (eq : has-dec-eq A)
  where

open import Spaces.WedgeCircles A renaming (wedge-circles to WA; base to baseWA)
open import Algebra.FreeGroup A renaming (freegroup to FA)
open import Algebra.FreeGroupProps A
open import Algebra.FreeGroupAsReducedWords A eq
open import Spaces.FlatteningLoopSpaceWedgeCircles A (dec-eq-is-set eq)

-- We can now prove that [tot-cover] is contractible using [CA-rec]
-- (because [CA-rec] means that [tot-cover] is the Cayley graph of FA)
P-CA-contr : (x : tot-cover) → Set _
P-CA-contr x = x ≡ CA-z e

-- We first prove it on points coming from reduced words
CA-contr-base-reduced-word : (w : reduced-word)
  → P-CA-contr (CA-z (reduced-to-freegroup w))
CA-contr-base-reduced-word (ε , red) = refl
CA-contr-base-reduced-word ((x ∷ w) , red) =
  ! (CA-e x _)
  ∘ CA-contr-base-reduced-word (w , tail-is-reduced x w red)
CA-contr-base-reduced-word ((x ′∷ w) , red) =
  (CA-e x _ ∘ ap CA-z (right-inverse-· x _))
  ∘ CA-contr-base-reduced-word (w , tail'-is-reduced x w red)

-- Then on every point
CA-contr-base : (u : FA) → P-CA-contr (CA-z u)
CA-contr-base u =
  ap CA-z (! (inv₂ u)) ∘ (CA-contr-base-reduced-word (freegroup-to-reduced u))

-- Now we prove that it’s true on paths, coming from reduced words
abstract
  CA-contr-loop-reduced-word : (t : A) (w : reduced-word) →
    (ap CA-z (reduced-to-freegroup-mul-reduce t w)
    ∘ ! (CA-e t (reduced-to-freegroup w)))
    ∘ (CA-contr-base-reduced-word w)
    ≡ CA-contr-base-reduced-word (mul-reduce t w)
  CA-contr-loop-reduced-word t (ε , red) = refl
  CA-contr-loop-reduced-word t ((x ∷ w) , red) = refl
  CA-contr-loop-reduced-word t ((x ′∷ w) , red) with (eq t x)
  CA-contr-loop-reduced-word x ((.x ′∷ w) , red) | inl refl =
    -- With the notations below, what we have to prove
    -- is [ (ap CA-z (! p) ∘ ! q) ∘ ((q ∘ ap CA-z p) ∘ r) ≡ r ]
    concat-assoc (ap CA-z (! p)) _ _
    ∘ (ap (λ t₁ → t₁ ∘ (! q ∘ ((q ∘ ap CA-z p) ∘ r))) (ap-opposite CA-z p)
    ∘ move!-right-on-left (ap CA-z p) (! q ∘ ((q ∘ ap CA-z p) ∘ r)) r
      (move!-right-on-left q ((q ∘ ap CA-z p) ∘ r) (ap CA-z p ∘ r)
      (concat-assoc q _ _))) where
    fw : FA
    fw = reduced-to-freegroup (w , tail'-is-reduced x w red)

    p : x · (x ⁻¹· fw) ≡ fw
    p = right-inverse-· x fw

    q : CA-z (x ⁻¹· fw) ≡ CA-z (x · (x ⁻¹· fw))
    q = CA-e x (x ⁻¹· fw)

    r : CA-z fw ≡ CA-z e
    r = CA-contr-base-reduced-word (w , tail'-is-reduced x w red)
  CA-contr-loop-reduced-word t ((x ′∷ w) , red) | inr different = refl

-- And finally for every path
CA-contr-loop : (t : A) (u : FA)
  → transport P-CA-contr (CA-e t u) (CA-contr-base u) ≡ (CA-contr-base (t · u))
CA-contr-loop t u =
  -- Idea:
  --
  -- We need to prove
  --   [p u ∘ (ap CA-z (q u) ∘ for-red u)
  --    ≡ ap CA-z (q (t · u)) ∘ for-red (t · u)]
  --
  -- [CA-contr-loop-reduced-word] gives
  -- that [(ap CA-z comp ∘ p (k u)) ∘ for-red u ≡ for-red (t · u)]

  trans-id≡cst (CA-e t u) (CA-contr-base u)
  ∘ (! (concat-assoc (p u) (ap CA-z (q u)) (for-red u))
  ∘ (whisker-right (for-red u) {q = p u ∘ ap CA-z (q u)}
       {r = ap CA-z (q (t · u)) ∘ (ap CA-z comp ∘ p (k u))}
    (! (homotopy-naturality f g p (q u))
    ∘ (whisker-right (p (k u)) {q = ap f (q u)}
         {r = ap CA-z (q (t · u)) ∘ ap CA-z comp}
      (ap-compose CA-z (λ u₁ → t · u₁) (q u)
      ∘ (ap (ap CA-z) (π₁ (freegroup-is-set _ _ _ _))
      ∘ ap-concat CA-z (q (t · u)) comp))
    ∘ concat-assoc (ap CA-z (q (t · u))) (ap CA-z comp) (p (k u))))
  ∘ (concat-assoc (ap CA-z (q (t · u))) (ap CA-z comp ∘ p (k u))
       (for-red u)
       ∘ whisker-left (ap CA-z (q (t · u)))
           auie))) where
  f : FA → tot-cover
  f u = CA-z (t · u)

  g : FA → tot-cover
  g u = CA-z u

  p : (u : FA) → f u ≡ g u
  p u = ! (CA-e t u)

  k : FA → FA
  k u = reduced-to-freegroup (freegroup-to-reduced u)

  q : (u : FA) → u ≡ k u
  q u = ! (inv₂ u)

  for-red : (u : FA) → CA-z (k u) ≡ CA-z e
  for-red u = CA-contr-base-reduced-word (freegroup-to-reduced u)

  comp : k (t · u) ≡ t · (k u)
  comp = reduced-to-freegroup-mul-reduce t (freegroup-to-reduced u)

  auie : (ap CA-z comp ∘ p (k u)) ∘ for-red u ≡ for-red (t · u)
  auie = CA-contr-loop-reduced-word t (freegroup-to-reduced u)

-- Hence, [CA] is contractible
CA-contr : (x : tot-cover) → P-CA-contr x
CA-contr = equivCA.CA-rec P-CA-contr CA-contr-base CA-contr-loop

abstract
  tot-cover-is-contr : is-contr tot-cover
  tot-cover-is-contr = (CA-z e , λ x → CA-contr x)

-- We define now a fiberwise map between the two fibrations [path-fib]
-- and [universal-cover]
fiberwise-map : (x : WA) → (path-fib x → universal-cover x)
fiberwise-map x q = transport universal-cover (! q) e

-- This induces an equivalence on the total spaces, because both total spaces
-- are contractible
total-equiv : is-equiv (total-map fiberwise-map)
total-equiv = contr-to-contr-is-equiv (total-map fiberwise-map)
                                      tot-path-fib-is-contr
                                      tot-cover-is-contr

-- Hence an equivalence fiberwise
fiberwise-map-is-equiv : (x : WA) → is-equiv (fiberwise-map x)
fiberwise-map-is-equiv x = fiberwise-is-equiv fiberwise-map total-equiv x

-- We can then conclude that the based loop space of the wedge of circles on [A]
-- is equivalent to the free group on [A], where [A] is any discrete set (i.e.
-- with decidable equality)
ΩWA≃FA : (baseWA ≡ baseWA) ≃ FA
ΩWA≃FA = (fiberwise-map baseWA , fiberwise-map-is-equiv baseWA)

