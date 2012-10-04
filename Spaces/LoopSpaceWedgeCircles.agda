{-# OPTIONS --without-K #-}

open import Base
open import Integers

module Spaces.LoopSpaceWedgeCircles {i} (A : Set i) (eq : dec-eq A) where

import Spaces.WedgeCircles
import Algebra.FreeGroup
import Algebra.FreeGroupProps
import Algebra.FreeGroupAsReducedWords

open Spaces.WedgeCircles A renaming (wedge-circles to WA)
open Algebra.FreeGroup A renaming (freegroup to FA)
open Algebra.FreeGroupProps A
open Algebra.FreeGroupAsReducedWords A eq

-- Path fibration

path-fib : WA → Set (suc i)
path-fib t = (t ≡ base)

tot-path-fib : Set (suc i)
tot-path-fib = Σ (WA) path-fib

abstract
  tot-path-fib-is-contr : is-contr tot-path-fib
  tot-path-fib-is-contr = pathto-is-contr base

-- Universal cover

x·-path : A → FA ≡ FA
x·-path x = eq-to-path (_ , x·-is-equiv x)

universal-cover : WA → Set i
universal-cover = wedge-circles-rec-nondep (Set _) FA x·-path

tot-cover : Set _
tot-cover = Σ WA universal-cover

trans-universal-cover : {u v : WA} (p : u ≡ v) (q : universal-cover u)
  → transport universal-cover p q
    ≡ transport (λ A → A) (map universal-cover p) q
trans-universal-cover (refl _) _ = refl _

abstract
  loops-to-x· : (t : A) (u : FA) → transport universal-cover (loops t) u ≡ t · u
  loops-to-x· t u =
    trans-universal-cover (loops t) u
    ∘ (map (λ t' → transport (λ B → B) t' u) (β-nondep (Set _) FA x·-path t)
    ∘ trans-X-eq-to-path (_ , x·-is-equiv t) u)

{-
Here is an HIT declaration for the Cayley graph of the free group over A:

data cayley : Set where
  z : FA → cayley
  e : (t : A) (u : FA) → z u ≡ z (t · u)

We will see that [cayley] is contractible.
We want to show that [tot-cover] has the same introduction and elimination
rules, so that we can prove that [tot-cover] is contractible too.
We do not need to actually have the type [cayley], it is enough to show
that [tot-cover] has the same rules and then we can copy the proof of the
contractibility using the new rules.
-}

-- Introduction rules
CA-z : FA → tot-cover
CA-z u = (base , u)

CA-e : (t : A) (u : FA) → CA-z u ≡ CA-z (t · u)
CA-e t u = total-path (loops t) (loops-to-x· t u)

-- Elimination rule
module equivCA
  {i}
  (P : tot-cover → Set i)
  (z : (u : FA) → P (CA-z u))
  (e : (t : A) (u : FA) → transport P (CA-e t u) (z u) ≡ z (t · u)) where

  CA-e' : (t : A) (u : FA)
    → CA-z u ≡ CA-z (transport universal-cover (loops t) u)
  CA-e' t u = total-path (loops t) (refl _)

  abstract
    e' : (t : A) (u : FA)
      → transport P (CA-e' t u) (z u)
        ≡ z (transport universal-cover (loops t) u)
    e' t u = (trans-totalpath {P = universal-cover} {Q = P} {x = (base , u)}
               {y = (base , transport universal-cover (loops t) u)} (loops t)
               (refl _) z
             ∘ move!-transp-left (λ z → P (base , z)) _ (loops-to-x· t u)
                                 (z (t · u))
             (! (trans-totalpath {P = universal-cover} {Q = P} {x = (base , u)}
                  {y = (base , (t · u))} (loops t) (loops-to-x· t u) z)
              ∘ e t u))
              ∘ map-dep z (! (loops-to-x· t u))

  P-base : (u : universal-cover (base)) → P (base , u)
  P-base u = z u

  abstract
    P-loops : (t : A) (u : universal-cover (base))
      → transport (λ x → (t : universal-cover x) → P (x , t)) (loops t) P-base u
        ≡ P-base u
    P-loops t u =
      transport (λ u → transport (λ x → (t : universal-cover x) → P (x , t))
                                 (loops t) P-base u ≡ P-base u)
        (trans-trans-opposite {P = universal-cover} (loops t) u)
        (! (trans-totalpath {P = universal-cover} {Q = P}
             {x = (base , transport universal-cover (! (loops t)) u)}
             {y = (base , transport universal-cover (loops t)
               (transport universal-cover (! (loops t)) u))}
             (loops t) (refl _) z)
        ∘ e' t (transport universal-cover (! (loops t)) u))

  P-CA-rec : (x : WA) → (t : universal-cover x) → P (x , t)
  P-CA-rec = wedge-circles-rec (λ x → (t : universal-cover x) → P (x , t))
                               P-base (λ t → funext-dep (P-loops t))

  -- Here is the conclusion of the elimination rule
  abstract
    CA-rec : (t : tot-cover) → P t
    CA-rec (x , y) = P-CA-rec x y
