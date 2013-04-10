{-# OPTIONS --without-K #-}

open import Base

module Algebra.FreeGroupAsReducedWords {i} (A : Set i) (eq : has-dec-eq A) where

A-is-set : is-set A
A-is-set = dec-eq-is-set eq

data word : Set i where
  ε : word
  _∷_ : A → word → word
  _′∷_ : A → word → word

is-reduced : word → Set i
is-reduced ε = unit
is-reduced (x ∷ ε) = unit
is-reduced (x ∷ (y ∷ w)) = is-reduced (y ∷ w)
is-reduced (x ∷ (y ′∷ w)) = (x ≢ y) × is-reduced (y ′∷ w)
is-reduced (x ′∷ ε) = unit
is-reduced (x ′∷ (y ∷ w)) = (x ≢ y) × is-reduced (y ∷ w)
is-reduced (x ′∷ (y ′∷ w)) = is-reduced (y ′∷ w)

is-reduced-is-prop : (w : word) → is-prop (is-reduced w)
is-reduced-is-prop ε = unit-is-prop
is-reduced-is-prop (x ∷ ε) = unit-is-prop
is-reduced-is-prop (x ∷ (y ∷ w)) = is-reduced-is-prop (y ∷ w)
is-reduced-is-prop (x ∷ (y ′∷ w)) =
  ×-is-truncated _ (Π-is-truncated _ (λ _ → λ ())) (is-reduced-is-prop (y ′∷ w))
is-reduced-is-prop (x ′∷ ε) = unit-is-prop
is-reduced-is-prop (x ′∷ (y ∷ w)) =
  ×-is-truncated _ (Π-is-truncated _ (λ _ → λ ())) (is-reduced-is-prop (y ∷ w))
is-reduced-is-prop (x ′∷ (y ′∷ w)) = is-reduced-is-prop (y ′∷ w)

reduced-word : Set i
reduced-word = Σ word is-reduced

word-total-path : {x y : A} (p : x ≡ y) {v w : word} (q : v ≡ w)
  → (x ∷ v ≡ y ∷ w)
word-total-path refl refl = refl

word'-total-path : {x y : A} (p : x ≡ y) {v w : word} (q : v ≡ w)
  → (x ′∷ v ≡ y ′∷ w)
word'-total-path refl refl = refl

-- The following six functions prove things like if [x ∷ v ≡ y ∷ w],
-- then [x ≡ y].
-- This is not as easy as it sounds, you cannot directly induct on the equality
-- (because [x ∷ v] is not a general element of type word), so you have to
-- extract the head, but it’s not always possible…

word-comp-path-type : (v w : word) → Set i
word-comp-path-type ε ε = unit
word-comp-path-type ε (y ∷ w) = ⊥
word-comp-path-type ε (y ′∷ w) = ⊥
word-comp-path-type (x ∷ v) ε = ⊥
word-comp-path-type (x ∷ v) (y ∷ w) = (x ≡ y) × (v ≡ w)
word-comp-path-type (x ∷ v) (y ′∷ w) = ⊥
word-comp-path-type (x ′∷ v) ε = ⊥
word-comp-path-type (x ′∷ v) (y ∷ w) = ⊥
word-comp-path-type (x ′∷ v) (y ′∷ w) = (x ≡ y) × (v ≡ w)

word-comp-path : {v w : word} (p : v ≡ w) → word-comp-path-type v w
word-comp-path {v = ε}      refl = tt
word-comp-path {v = x  ∷ v} refl = (refl , refl)
word-comp-path {v = x ′∷ v} refl = (refl , refl)

word-base-path : {x y : A} {v w : word} (p : x ∷ v ≡ y ∷ w) → x ≡ y
word-base-path p = π₁ (word-comp-path p)

word-fiber-path : {x y : A} {v w : word} (p : x ∷ v ≡ y ∷ w) → v ≡ w
word-fiber-path p = π₂ (word-comp-path p)

word'-base-path : {x y : A} {v w : word} (p : x ′∷ v ≡ y ′∷ w) → x ≡ y
word'-base-path p = π₁ (word-comp-path p)

word'-fiber-path : {x y : A} {v w : word} (p : x ′∷ v ≡ y ′∷ w) → v ≡ w
word'-fiber-path p = π₂ (word-comp-path p)

-- This one goes to Set and is used to prove that the constructors of [word] are
-- disjoint
word-cst-dis : (v w : word) → Set
word-cst-dis ε ε = unit
word-cst-dis ε (y ∷ w) = ⊥
word-cst-dis ε (y ′∷ w) = ⊥
word-cst-dis (x ∷ v) ε = ⊥
word-cst-dis (x ∷ v) (y ∷ w) = unit
word-cst-dis (x ∷ v) (y ′∷ w) = ⊥
word-cst-dis (x ′∷ v) ε = ⊥
word-cst-dis (x ′∷ v) (y ∷ w) = ⊥
word-cst-dis (x ′∷ v) (y ′∷ w) = unit

word-has-dec-eq : has-dec-eq word
word-has-dec-eq ε ε = inl refl
word-has-dec-eq ε (x ∷ w) = inr (λ p → transport (word-cst-dis ε) p tt)
word-has-dec-eq ε (x ′∷ w) = inr (λ p → transport (word-cst-dis ε) p tt)
word-has-dec-eq (x ∷ v) ε = inr (λ p → transport (word-cst-dis (x ∷ v)) p tt)
word-has-dec-eq (x ∷ v) (y ∷ w) with (eq x y)
word-has-dec-eq (x ∷ v) (y ∷ w) | inl x≡y with (word-has-dec-eq v w)
word-has-dec-eq (x ∷ v) (y ∷ w) | inl x≡y | inl v≡w =
  inl (word-total-path x≡y v≡w)
word-has-dec-eq (x ∷ v) (y ∷ w) | inl x≡y | inr v≢w =
  inr (λ p → v≢w (word-fiber-path p))
word-has-dec-eq (x ∷ v) (y ∷ w) | inr x≢y = inr (λ p → x≢y (word-base-path p))
word-has-dec-eq (x ∷ v) (y ′∷ w) =
  inr (λ p → transport (word-cst-dis (x ∷ v)) p tt)
word-has-dec-eq (x ′∷ v) ε = inr (λ p → transport (word-cst-dis (x ′∷ v)) p tt)
word-has-dec-eq (x ′∷ v) (y ∷ w) =
  inr (λ p → transport (word-cst-dis (x ′∷ v)) p tt)
word-has-dec-eq (x ′∷ v) (y ′∷ w) with (eq x y)
word-has-dec-eq (x ′∷ v) (y ′∷ w) | inl x≡y with (word-has-dec-eq v w)
word-has-dec-eq (x ′∷ v) (y ′∷ w) | inl x≡y | inl v≡w =
  inl (word'-total-path x≡y v≡w)
word-has-dec-eq (x ′∷ v) (y ′∷ w) | inl x≡y | inr v≢w =
  inr (λ p → v≢w (word'-fiber-path p))
word-has-dec-eq (x ′∷ v) (y ′∷ w) | inr x≢y =
  inr (λ p → x≢y (word'-base-path p))

word-is-set : is-set word
word-is-set = dec-eq-is-set word-has-dec-eq

abstract
  reduced-is-set : is-set reduced-word
  reduced-is-set =
    subtype-truncated-S-is-truncated-S _ word-is-set is-reduced-is-prop

tail-is-reduced : (x : A) (w : word) (r : is-reduced (x ∷ w)) → is-reduced w
tail-is-reduced x ε red = tt
tail-is-reduced x (y ∷ w) red = red
tail-is-reduced x (y ′∷ w) red = π₂ red

tail'-is-reduced : (x : A) (w : word) (r : is-reduced (x ′∷ w)) → is-reduced w
tail'-is-reduced x ε red = tt
tail'-is-reduced x (y ∷ w) red = π₂ red
tail'-is-reduced x (y ′∷ w) red = red

import Algebra.FreeGroup as F
open F A
import Algebra.FreeGroupProps as Fp
open Fp A

reduced-to-freegroup : reduced-word → freegroup
reduced-to-freegroup (ε , _) = e
reduced-to-freegroup ((x ∷ w) , r) =
  x · reduced-to-freegroup (w , tail-is-reduced x w r)
reduced-to-freegroup ((x ′∷ w) , r) =
  x ⁻¹· reduced-to-freegroup (w , tail'-is-reduced x w r)

mul-reduce : A → reduced-word → reduced-word
mul-reduce x (ε , red) = ((x ∷ ε) , tt)
mul-reduce x ((y ∷ w) , red) = ((x ∷ (y ∷ w)) , red)
mul-reduce x ((y ′∷ w) , red) with (eq x y)
mul-reduce x ((y ′∷ w) , red) | inl equal = (w , tail'-is-reduced y w red)
mul-reduce x ((y ′∷ w) , red) | inr different =
  ((x ∷ (y ′∷ w)) , (different , red))

mul'-reduce : A → reduced-word → reduced-word
mul'-reduce x (ε , red) = ((x ′∷ ε) , tt)
mul'-reduce x ((y ∷ w) , red) with (eq x y)
mul'-reduce x ((y ∷ w) , red) | inl equal = (w , tail-is-reduced y w red)
mul'-reduce x ((y ∷ w) , red) | inr different =
  ((x ′∷ (y ∷ w)) , (different , red))
mul'-reduce x ((y ′∷ w) , red) = (x ′∷ (y ′∷ w)) , red

abstract
  mul-mul'-reduce : (x : A) (w : reduced-word)
    → mul-reduce x (mul'-reduce x w) ≡ w
  mul-mul'-reduce x (ε , red) with (eq x x)
  mul-mul'-reduce x (ε , red) | inl obvious = refl
  mul-mul'-reduce x (ε , red) | inr absurd = abort-nondep (absurd refl)
  mul-mul'-reduce x ((y ∷ w) , red) with (eq x y)
  mul-mul'-reduce x ((y ∷ ε) , red) | inl equal = ap _ equal
  mul-mul'-reduce x ((y ∷ (z ∷ w)) , red) | inl equal = ap _ equal
  mul-mul'-reduce x ((y ∷ (z ′∷ w)) , red) | inl equal with (eq x z)
  mul-mul'-reduce x ((y ∷ (z ′∷ w)) , red) | inl equal | inl absurd =
    abort-nondep (π₁ red (! equal ∘ absurd))
  mul-mul'-reduce x ((y ∷ (z ′∷ w)) , red) | inl equal | inr obvious =
    Σ-eq (ap _ equal) (π₁ (is-reduced-is-prop (y ∷ (z ′∷ w)) _ _))
  mul-mul'-reduce x ((y ∷ w) , red) | inr different with (eq x x)
  mul-mul'-reduce x ((y ∷ w) , red) | inr different | inl obvious = refl
  mul-mul'-reduce x ((y ∷ w) , red) | inr different | inr absurd =
    abort-nondep (absurd refl)
  mul-mul'-reduce x ((y ′∷ w) , red) with (eq x x)
  mul-mul'-reduce x ((y ′∷ w) , red) | inl obvious = refl
  mul-mul'-reduce x ((y ′∷ w) , red) | inr absurd =
    abort-nondep (absurd refl)

abstract
  mul'-mul-reduce : (x : A) (w : reduced-word)
    → mul'-reduce x (mul-reduce x w) ≡ w
  mul'-mul-reduce x (ε , red) with (eq x x)
  mul'-mul-reduce x (ε , red) | inl obvious = refl
  mul'-mul-reduce x (ε , red) | inr absurd = abort-nondep (absurd refl)
  mul'-mul-reduce x ((y ′∷ w) , red) with (eq x y)
  mul'-mul-reduce x ((y ′∷ ε) , red) | inl equal = ap _ equal
  mul'-mul-reduce x ((y ′∷ (z ′∷ w)) , red) | inl equal = ap _ equal
  mul'-mul-reduce x ((y ′∷ (z ∷ w)) , red) | inl equal with (eq x z)
  mul'-mul-reduce x ((y ′∷ (z ∷ w)) , red) | inl equal | inl absurd =
    abort-nondep (π₁ red (! equal ∘ absurd))
  mul'-mul-reduce x ((y ′∷ (z ∷ w)) , red) | inl equal | inr obvious =
    Σ-eq (ap _ equal) (π₁ (is-reduced-is-prop (y ′∷ (z ∷ w)) _ _))
  mul'-mul-reduce x ((y ′∷ w) , red) | inr different with (eq x x)
  mul'-mul-reduce x ((y ′∷ w) , red) | inr different | inl obvious = refl
  mul'-mul-reduce x ((y ′∷ w) , red) | inr different | inr absurd =
    abort-nondep (absurd refl)
  mul'-mul-reduce x ((y ∷ w) , red) with (eq x x)
  mul'-mul-reduce x ((y ∷ w) , red) | inl obvious = refl
  mul'-mul-reduce x ((y ∷ w) , red) | inr absurd =
    abort-nondep (absurd refl)

freegroup-to-reduced : freegroup → reduced-word
freegroup-to-reduced = freegroup-rec-nondep reduced-word
  (ε , tt)
  mul-reduce
  mul'-reduce
  mul-mul'-reduce
  mul'-mul-reduce
  reduced-is-set

abstract
  mul-reduce-reduced : (x : A) (w : word) (red : is-reduced (x ∷ w))
    → mul-reduce x (w , tail-is-reduced x w red) ≡ ((x ∷ w) , red)
  mul-reduce-reduced x ε red = refl
  mul-reduce-reduced x (y ∷ w) red = refl
  mul-reduce-reduced x (y ′∷ w) red with (eq x y)
  mul-reduce-reduced x (y ′∷ w) red | inl absurd = abort-nondep (π₁ red absurd)
  mul-reduce-reduced x (y ′∷ w) red | inr obvious =
    Σ-eq refl (π₁ (is-reduced-is-prop (x ∷ (y ′∷ w)) _ _))

abstract
  mul'-reduce-reduced : (x : A) (w : word) (red : is-reduced (x ′∷ w))
    → mul'-reduce x (w , tail'-is-reduced x w red) ≡ ((x ′∷ w) , red)
  mul'-reduce-reduced x ε red = refl
  mul'-reduce-reduced x (y ∷ w) red with (eq x y)
  mul'-reduce-reduced x (y ∷ w) red | inl absurd = abort-nondep (π₁ red absurd)
  mul'-reduce-reduced x (y ∷ w) red | inr obvious =
    Σ-eq refl (π₁ (is-reduced-is-prop (x ′∷ (y ∷ w)) _ _))
  mul'-reduce-reduced x (y ′∷ w) red = refl

inv₁ : (w : reduced-word) → freegroup-to-reduced (reduced-to-freegroup w) ≡ w
inv₁ (ε , red) = refl
inv₁ ((x ∷ w) , red) = ap (mul-reduce x) (inv₁ (w , tail-is-reduced x w red))
                       ∘ mul-reduce-reduced x w red
inv₁ ((x ′∷ w) , red) =
  ap (mul'-reduce x) (inv₁ (w , tail'-is-reduced x w red))
  ∘ mul'-reduce-reduced x w red

reduced-to-freegroup-mul-reduce : (x : A) (v : reduced-word)
  → reduced-to-freegroup (mul-reduce x v) ≡ x · (reduced-to-freegroup v)
reduced-to-freegroup-mul-reduce x (ε , red) = refl
reduced-to-freegroup-mul-reduce x ((y ∷ v) , red) = refl
reduced-to-freegroup-mul-reduce x ((y ′∷ v) , red) with (eq x y)
reduced-to-freegroup-mul-reduce x ((.x ′∷ v) , red) | inl refl =
  ! (right-inverse-· x (reduced-to-freegroup (v , tail'-is-reduced x v red)))
reduced-to-freegroup-mul-reduce x ((y ′∷ v) , red) | inr different = refl

reduced-to-freegroup-mul'-reduce : (x : A) (v : reduced-word)
  → reduced-to-freegroup (mul'-reduce x v) ≡ x ⁻¹· (reduced-to-freegroup v)
reduced-to-freegroup-mul'-reduce x (ε , red) = refl
reduced-to-freegroup-mul'-reduce x ((y ∷ v) , red) with (eq x y)
reduced-to-freegroup-mul'-reduce x ((.x ∷ v) , red) | inl refl =
  ! (left-inverse-· x (reduced-to-freegroup (v , tail-is-reduced x v red)))
reduced-to-freegroup-mul'-reduce x ((y ∷ v) , red) | inr different = refl
reduced-to-freegroup-mul'-reduce x ((y ′∷ v) , red) = refl

inv₂ : (a : freegroup) → reduced-to-freegroup (freegroup-to-reduced a) ≡ a
inv₂ = freegroup-rec _
  refl
  (λ x u p → reduced-to-freegroup-mul-reduce x (freegroup-to-reduced u)
             ∘ ap (λ t → x · t) {y = u} p)
  (λ x u p → reduced-to-freegroup-mul'-reduce x (freegroup-to-reduced u)
             ∘ ap (λ t → x ⁻¹· t) {y = u} p)
  (λ x u t → π₁ (freegroup-is-set _ _ _ _))
  (λ x u t → π₁ (freegroup-is-set _ _ _ _))
  (λ u → truncated-is-truncated-S _ (freegroup-is-set _ _))

freegroup-equiv-reduced : freegroup ≃ reduced-word
freegroup-equiv-reduced =
  (freegroup-to-reduced , iso-is-eq _ reduced-to-freegroup inv₁ inv₂)
