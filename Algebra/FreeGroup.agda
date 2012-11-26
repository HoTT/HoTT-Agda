{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.TruncatedHIT
open import Integers

module Algebra.FreeGroup {i} (A : Set i) where

{-
The definition is the following

    (0)data freegroup : Set i where
      e : freegroup
      _·_   : A → freegroup → freegroup
      _⁻¹·_ : A → freegroup → freegroup
      right-inverse-· : (x : A) (u : freegroup) → x · (x ⁻¹· u) ≡ u
      left-inverse-·  : (x : A) (u : freegroup) → x ⁻¹· (x · u) ≡ u

("(0)data" means that it’s a higher inductive 0-truncated type)
-}

private
  data #freegroup : Set i where
    #e  : #freegroup
    #·  : A → #freegroup → #freegroup
    #⁻¹· : A → #freegroup → #freegroup

    #top : (f : hSⁿ ⟨0⟩ → #freegroup) → #freegroup

freegroup : Set i
freegroup = #freegroup

e : freegroup
e = #e

_·_ : A → freegroup → freegroup
_·_ = #·

_⁻¹·_ : A → freegroup → freegroup
_⁻¹·_ = #⁻¹·

postulate  -- HIT
  right-inverse-· : (x : A) (u : freegroup) → x · (x ⁻¹· u) ≡ u
  left-inverse-·  : (x : A) (u : freegroup) → x ⁻¹· (x · u) ≡ u

top : (f : hSⁿ ⟨0⟩ → freegroup) → freegroup
top = #top

postulate  -- HIT
  rays : (f : hSⁿ ⟨0⟩ → freegroup) (x : hSⁿ ⟨0⟩) → top f ≡ f x

#freegroup-rec : ∀ {j} (P : freegroup → Set j)
  (base : P e)
  (g   : (x : A) (u : freegroup) → P u → P (x · u))
  (g'  : (x : A) (u : freegroup) → P u → P (x ⁻¹· u))
  (gg' : (x : A) (u : freegroup) (t : P u)
         → transport P (right-inverse-· x u) (g x _ (g' x u t)) ≡ t)
  (g'g : (x : A) (u : freegroup) (t : P u)
         → transport P (left-inverse-· x u) (g' x _ (g x u t)) ≡ t)
  (top* :  (f : hSⁿ ⟨0⟩ → freegroup) (p : (x : hSⁿ ⟨0⟩) → P (f x)) → P (top f))
  (rays* : (f : hSⁿ ⟨0⟩ → freegroup) (p : (x : hSⁿ ⟨0⟩) → P (f x)) (x : hSⁿ ⟨0⟩)
         → transport P (rays f x) (top* f p) ≡ p x)
  → ((t : freegroup) → P t)
#freegroup-rec P base g g' gg' g'g top* rays* #e = base
#freegroup-rec P base g g' gg' g'g top* rays* (#· x u) =
  g x u (#freegroup-rec P base g g' gg' g'g top* rays* u)
#freegroup-rec P base g g' gg' g'g top* rays* (#⁻¹· x u) =
  g' x u (#freegroup-rec P base g g' gg' g'g top* rays* u)
#freegroup-rec P base g g' gg' g'g top* rays* (#top f) =
  top* f (λ x → #freegroup-rec P base g g' gg' g'g top* rays* (f x))

#freegroup-rec-nondep : ∀ {j} (B : Set j)
  (base : B)
  (g   : A → B → B)
  (g'  : A → B → B)
  (gg' : (x : A) (u : B) → (g x (g' x u)) ≡ u)
  (g'g : (x : A) (u : B) → (g' x (g x u)) ≡ u)
  (top* :  (f : hSⁿ ⟨0⟩ → freegroup) (p : hSⁿ ⟨0⟩ → B) → B)
  (rays* : (f : hSⁿ ⟨0⟩ → freegroup) (p : hSⁿ ⟨0⟩ → B) (x : hSⁿ ⟨0⟩)
    → top* f p ≡ p x)
  → freegroup → B
#freegroup-rec-nondep P base g g' gg' g'g top* rays* #e = base
#freegroup-rec-nondep P base g g' gg' g'g top* rays* (#· x u) =
  g x (#freegroup-rec-nondep P base g g' gg' g'g top* rays* u)
#freegroup-rec-nondep P base g g' gg' g'g top* rays* (#⁻¹· x u) =
  g' x (#freegroup-rec-nondep P base g g' gg' g'g top* rays* u)
#freegroup-rec-nondep P base g g' gg' g'g top* rays* (#top f) =
  top* f (λ x → #freegroup-rec-nondep P base g g' gg' g'g top* rays* (f x))

freegroup-rec : ∀ {j} (P : freegroup → Set j)
  (base : P e)
  (g   : (x : A) (u : freegroup) → P u → P (x · u))
  (g'  : (x : A) (u : freegroup) → P u → P (x ⁻¹· u))
  (gg' : (x : A) (u : freegroup) (t : P u)
         → transport P (right-inverse-· x u) (g x _ (g' x u t)) ≡ t)
  (g'g : (x : A) (u : freegroup) (t : P u)
         → transport P (left-inverse-· x u) (g' x _ (g x u t)) ≡ t)
  (p : (u : freegroup) → is-set (P u))
  → ((t : freegroup) → P t)
freegroup-rec P base g g' gg' g'g p =
  #freegroup-rec P base g g' gg' g'g
                 (λ f p₁ → π₁ (u f p₁))
                 (λ f p₁ → π₂ (u f p₁)) where
  u = truncated-has-filling-dep freegroup P ⟨0⟩ (λ ()) (λ f → (top f , rays f))

freegroup-rec-nondep : ∀ {j} (B : Set j)
  (base : B)
  (g   : A → B → B)
  (g'  : A → B → B)
  (gg' : (x : A) (u : B) → (g x (g' x u)) ≡ u)
  (g'g : (x : A) (u : B) → (g' x (g x u)) ≡ u)
  (p : is-set B)
  → freegroup → B
freegroup-rec-nondep B base g g' gg' g'g p =
  #freegroup-rec-nondep B base g g' gg' g'g
                        (λ _ p → π₁ (u p))
                        (λ _ p → π₂ (u p)) where
  u = truncated-has-spheres-filled ⟨0⟩ _ p
