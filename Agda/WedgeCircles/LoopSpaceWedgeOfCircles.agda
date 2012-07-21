{-# OPTIONS --without-K #-}

open import Base
open import Integers.Integers

module WedgeCircles.LoopSpaceWedgeOfCircles {i} (A : Set i) (eq : dec-eq A) where

import WedgeCircles.WedgeCircles
import FreeGroup.FreeGroup
import FreeGroup.FreeGroupProps
import FreeGroup.FreeGroupAsReducedWords

open WedgeCircles.WedgeCircles A renaming (wedge-circles to WA)
open FreeGroup.FreeGroup A renaming (freegroup to FA)
open FreeGroup.FreeGroupProps A
open FreeGroup.FreeGroupAsReducedWords A eq

P-path : WA → Set (suc i)
P-path t = (t ≡ base)

tot-path : Set _
tot-path = Σ (WA) P-path

x·-path : A → FA ≡ FA
x·-path x = eq-to-path (_ , x·-is-equiv x)

P-type : WA → Set i
P-type = wedge-circles-rec-nondep (Set _) FA x·-path

tot-type : Set _
tot-type = Σ WA P-type

abstract
  tot-path-is-contr : is-contr tot-path
  tot-path-is-contr = ((base , refl base) , pathto-is-contr)

trans-P-type : {u v : WA} (p : u ≡ v) (q : P-type u) → transport P-type p q ≡ transport (λ A → A) (map P-type p) q
trans-P-type (refl _) _ = refl _

abstract
  loops-to-x· : (t : A) (u : FA) → transport P-type (loops t) u ≡ t · u
  loops-to-x· t u = trans-P-type (loops t) u ∘ (map (λ t' → transport (λ B → B) t' u) (β-nondep (Set _) FA x·-path t)
    ∘ trans-eq-to-path (_ , x·-is-equiv t) u)

{-
Here is an HIT declaration for the Cayley graph of the free group over A:

data cayley : Set where
  z : FA → cayley
  e : (t : A) (u : FA) → z u ≡ z (t · u)

We will see that [cayley] is contractible.
We want to show that [tot-type] has the same introduction and elimination rules, so that we can prove that [tot-type] is contractible too.
We do not need to actually have the type [cayley], it is enough to show that [tot-type] has the same rules and then we can copy the proof of the
contractibility using the new rules.
-}

-- Introduction rules
CA-z : FA → tot-type
CA-z u = (base , u)

CA-e : (t : A) (u : FA) → CA-z u ≡ CA-z (t · u)
CA-e t u = total-path (loops t) (loops-to-x· t u)

-- Elimination rule
module equivCA
  {i}
  (P : tot-type → Set i)
  (z : (u : FA) → P (CA-z u))
  (e : (t : A) (u : FA) → transport P (CA-e t u) (z u) ≡ z (t · u)) where

  CA-e' : (t : A) (u : FA) → CA-z u ≡ CA-z (transport P-type (loops t) u)
  CA-e' t u = total-path (loops t) (refl _)

  abstract
    e' : (t : A) (u : FA) → transport P (CA-e' t u) (z u) ≡ z (transport P-type (loops t) u)
    e' t u = (trans-totalpath {P = P-type} {Q = P} {x = (base , u)} {y = (base , transport P-type (loops t) u)} (loops t) (refl _) z
         ∘ move!-transp-left (λ z → P (base , z)) _ (loops-to-x· t u) (z (t · u))
           (! (trans-totalpath {P = P-type} {Q = P} {x = (base , u)} {y = (base , (t · u))} (loops t) (loops-to-x· t u) z)
           ∘ e t u))
         ∘ map-dep z (! (loops-to-x· t u))

  P-base : (u : P-type (base)) → P (base , u)
  P-base u = z u

  abstract
    P-loops : (t : A) (u : P-type (base)) → transport (λ x → (t : P-type x) → P (x , t)) (loops t) P-base u ≡ P-base u
    P-loops t u = transport (λ u → transport (λ x → (t : P-type x) → P (x , t)) (loops t) P-base u ≡ P-base u)
             (trans-trans-opposite {P = P-type} (loops t) u)
             (! (trans-totalpath {P = P-type} {Q = P} {x = (base , transport P-type (! (loops t)) u)}
                                  {y = (base , transport P-type (loops t) (transport P-type (! (loops t)) u))} (loops t) (refl _) z)
             ∘ e' t (transport P-type (! (loops t)) u))

  P-CA-rec : (x : WA) → (t : P-type x) → P (x , t)
  P-CA-rec = wedge-circles-rec (λ x → (t : P-type x) → P (x , t)) P-base (λ t → funext-dep (P-loops t))

  -- Here is the conclusion of the elimination rule
  abstract
    CA-rec : (t : tot-type) → P t
    CA-rec (x , y) = P-CA-rec x y
