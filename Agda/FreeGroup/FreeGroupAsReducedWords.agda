{-# OPTIONS --without-K #-}

open import Base

module FreeGroup.FreeGroupAsReducedWords {i} (A : Set i) (eq : dec-eq A) where

A-is-set : is-set A
A-is-set = dec-eq-is-set A eq

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
is-reduced-is-prop (x ∷ (y ′∷ w)) = ×-hlevel 1 (pi-is-prop (λ _ → λ ()))
                                               (is-reduced-is-prop (y ′∷ w))
is-reduced-is-prop (x ′∷ ε) = unit-is-prop
is-reduced-is-prop (x ′∷ (y ∷ w)) = ×-hlevel 1 (pi-is-prop (λ _ → λ ()))
                                               (is-reduced-is-prop (y ∷ w))
is-reduced-is-prop (x ′∷ (y ′∷ w)) = is-reduced-is-prop (y ′∷ w)

reduced-word : Set i
reduced-word = Σ word is-reduced

word-total-path : {x y : A} (p : x ≡ y) {v w : word} (q : v ≡ w)
  → (x ∷ v ≡ y ∷ w)
word-total-path (refl _) (refl _) = refl _

word'-total-path : {x y : A} (p : x ≡ y) {v w : word} (q : v ≡ w)
  → (x ′∷ v ≡ y ′∷ w)
word'-total-path (refl _) (refl _) = refl _

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
word-comp-path (refl ε) = tt
word-comp-path (refl (x ∷ v)) = (refl _ , refl _)
word-comp-path (refl (x ′∷ v)) = (refl _ , refl _)

word-base-path : {x y : A} {v w : word} (p : x ∷ v ≡ y ∷ w) → x ≡ y
word-base-path p = π₁ (word-comp-path p)

word-fiber-path : {x y : A} {v w : word} (p : x ∷ v ≡ y ∷ w) → v ≡ w
word-fiber-path p = π₂ (word-comp-path p)

word'-base-path : {x y : A} {v w : word} (p : x ′∷ v ≡ y ′∷ w) → x ≡ y
word'-base-path p = π₁ (word-comp-path p)

word'-fiber-path : {x y : A} {v w : word} (p : x ′∷ v ≡ y ′∷ w) → v ≡ w
word'-fiber-path p = π₂ (word-comp-path p)

word-dec-eq : dec-eq word
word-dec-eq ε ε = inl (refl _)
word-dec-eq ε (x ∷ w) = inr (λ ())
word-dec-eq ε (x ′∷ w) = inr (λ ())
word-dec-eq (x ∷ v) ε = inr (λ ())
word-dec-eq (x ∷ v) (y ∷ w) with (eq x y)
word-dec-eq (x ∷ v) (y ∷ w) | inl x≡y with (word-dec-eq v w)
word-dec-eq (x ∷ v) (y ∷ w) | inl x≡y | inl v≡w = inl (word-total-path x≡y v≡w)
word-dec-eq (x ∷ v) (y ∷ w) | inl x≡y | inr v≢w =
  inr (λ p → v≢w (word-fiber-path p))
word-dec-eq (x ∷ v) (y ∷ w) | inr x≢y = inr (λ p → x≢y (word-base-path p))
word-dec-eq (x ∷ v) (y ′∷ w) = inr (λ ())
word-dec-eq (x ′∷ v) ε = inr (λ ())
word-dec-eq (x ′∷ v) (y ∷ w) = inr (λ ())
word-dec-eq (x ′∷ v) (y ′∷ w) with (eq x y)
word-dec-eq (x ′∷ v) (y ′∷ w) | inl x≡y with (word-dec-eq v w)
word-dec-eq (x ′∷ v) (y ′∷ w) | inl x≡y | inl v≡w =
  inl (word'-total-path x≡y v≡w)
word-dec-eq (x ′∷ v) (y ′∷ w) | inl x≡y | inr v≢w =
  inr (λ p → v≢w (word'-fiber-path p))
word-dec-eq (x ′∷ v) (y ′∷ w) | inr x≢y = inr (λ p → x≢y (word'-base-path p))

word-is-set : is-set word
word-is-set = dec-eq-is-set word word-dec-eq

abstract
  reduced-is-set : is-set reduced-word
  reduced-is-set = subset-is-set word is-reduced

tail-is-reduced : (x : A) (w : word) (r : is-reduced (x ∷ w)) → is-reduced w
tail-is-reduced x ε red = tt
tail-is-reduced x (y ∷ w) red = red
tail-is-reduced x (y ′∷ w) red = π₂ red

tail'-is-reduced : (x : A) (w : word) (r : is-reduced (x ′∷ w)) → is-reduced w
tail'-is-reduced x ε red = tt
tail'-is-reduced x (y ∷ w) red = π₂ red
tail'-is-reduced x (y ′∷ w) red = red

import FreeGroup.FreeGroup
open FreeGroup.FreeGroup A
import FreeGroup.FreeGroupProps
open FreeGroup.FreeGroupProps A

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
  mul-mul'-reduce x (ε , red) | inl obvious = refl _
  mul-mul'-reduce x (ε , red) | inr absurd = abort-nondep (absurd (refl _))
  mul-mul'-reduce x ((y ∷ w) , red) with (eq x y)
  mul-mul'-reduce x ((y ∷ ε) , red) | inl equal = map _ equal
  mul-mul'-reduce x ((y ∷ (z ∷ w)) , red) | inl equal = map _ equal
  mul-mul'-reduce x ((y ∷ (z ′∷ w)) , red) | inl equal with (eq x z)
  mul-mul'-reduce x ((y ∷ (z ′∷ w)) , red) | inl equal | inl absurd =
    abort-nondep (π₁ red (! equal ∘ absurd))
  mul-mul'-reduce x ((y ∷ (z ′∷ w)) , red) | inl equal | inr obvious =
    total-path (map _ equal) (π₁ (is-reduced-is-prop (y ∷ (z ′∷ w)) _ _))
  mul-mul'-reduce x ((y ∷ w) , red) | inr different with (eq x x)
  mul-mul'-reduce x ((y ∷ w) , red) | inr different | inl obvious = refl _
  mul-mul'-reduce x ((y ∷ w) , red) | inr different | inr absurd =
    abort-nondep (absurd (refl _))
  mul-mul'-reduce x ((y ′∷ w) , red) with (eq x x) 
  mul-mul'-reduce x ((y ′∷ w) , red) | inl obvious = refl _
  mul-mul'-reduce x ((y ′∷ w) , red) | inr absurd =
    abort-nondep (absurd (refl _))

abstract
  mul'-mul-reduce : (x : A) (w : reduced-word)
    → mul'-reduce x (mul-reduce x w) ≡ w
  mul'-mul-reduce x (ε , red) with (eq x x)
  mul'-mul-reduce x (ε , red) | inl obvious = refl _
  mul'-mul-reduce x (ε , red) | inr absurd = abort-nondep (absurd (refl _))
  mul'-mul-reduce x ((y ′∷ w) , red) with (eq x y)
  mul'-mul-reduce x ((y ′∷ ε) , red) | inl equal = map _ equal
  mul'-mul-reduce x ((y ′∷ (z ′∷ w)) , red) | inl equal = map _ equal
  mul'-mul-reduce x ((y ′∷ (z ∷ w)) , red) | inl equal with (eq x z)
  mul'-mul-reduce x ((y ′∷ (z ∷ w)) , red) | inl equal | inl absurd =
    abort-nondep (π₁ red (! equal ∘ absurd))
  mul'-mul-reduce x ((y ′∷ (z ∷ w)) , red) | inl equal | inr obvious =
    total-path (map _ equal) (π₁ (is-reduced-is-prop (y ′∷ (z ∷ w)) _ _))
  mul'-mul-reduce x ((y ′∷ w) , red) | inr different with (eq x x)
  mul'-mul-reduce x ((y ′∷ w) , red) | inr different | inl obvious = refl _
  mul'-mul-reduce x ((y ′∷ w) , red) | inr different | inr absurd =
    abort-nondep (absurd (refl _))
  mul'-mul-reduce x ((y ∷ w) , red) with (eq x x) 
  mul'-mul-reduce x ((y ∷ w) , red) | inl obvious = refl _
  mul'-mul-reduce x ((y ∷ w) , red) | inr absurd =
    abort-nondep (absurd (refl _))

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
  mul-reduce-reduced x ε red = refl _
  mul-reduce-reduced x (y ∷ w) red = refl _
  mul-reduce-reduced x (y ′∷ w) red with (eq x y)
  mul-reduce-reduced x (y ′∷ w) red | inl absurd = abort-nondep (π₁ red absurd)
  mul-reduce-reduced x (y ′∷ w) red | inr obvious =
    total-path (refl _) (π₁ (is-reduced-is-prop (x ∷ (y ′∷ w)) _ _))

abstract
  mul'-reduce-reduced : (x : A) (w : word) (red : is-reduced (x ′∷ w))
    → mul'-reduce x (w , tail'-is-reduced x w red) ≡ ((x ′∷ w) , red)
  mul'-reduce-reduced x ε red = refl _
  mul'-reduce-reduced x (y ∷ w) red with (eq x y)
  mul'-reduce-reduced x (y ∷ w) red | inl absurd = abort-nondep (π₁ red absurd)
  mul'-reduce-reduced x (y ∷ w) red | inr obvious =
    total-path (refl _) (π₁ (is-reduced-is-prop (x ′∷ (y ∷ w)) _ _))
  mul'-reduce-reduced x (y ′∷ w) red = refl _

inv₁ : (w : reduced-word) → freegroup-to-reduced (reduced-to-freegroup w) ≡ w
inv₁ (ε , red) = refl _
inv₁ ((x ∷ w) , red) = map (mul-reduce x) (inv₁ (w , tail-is-reduced x w red))
                       ∘ mul-reduce-reduced x w red
inv₁ ((x ′∷ w) , red) =
  map (mul'-reduce x) (inv₁ (w , tail'-is-reduced x w red))
  ∘ mul'-reduce-reduced x w red

reduced-to-freegroup-mul-reduce : (x : A) (v : reduced-word)
  → reduced-to-freegroup (mul-reduce x v) ≡ x · (reduced-to-freegroup v)
reduced-to-freegroup-mul-reduce x (ε , red) = refl _
reduced-to-freegroup-mul-reduce x ((y ∷ v) , red) = refl _
reduced-to-freegroup-mul-reduce x ((y ′∷ v) , red) with (eq x y)
reduced-to-freegroup-mul-reduce x ((.x ′∷ v) , red) | inl (refl .x) =
  ! (right-inverse-· x (reduced-to-freegroup (v , tail'-is-reduced x v red)))
reduced-to-freegroup-mul-reduce x ((y ′∷ v) , red) | inr different = refl _

reduced-to-freegroup-mul'-reduce : (x : A) (v : reduced-word)
  → reduced-to-freegroup (mul'-reduce x v) ≡ x ⁻¹· (reduced-to-freegroup v)
reduced-to-freegroup-mul'-reduce x (ε , red) = refl _
reduced-to-freegroup-mul'-reduce x ((y ∷ v) , red) with (eq x y)
reduced-to-freegroup-mul'-reduce x ((.x ∷ v) , red) | inl (refl .x) =
  ! (left-inverse-· x (reduced-to-freegroup (v , tail-is-reduced x v red)))
reduced-to-freegroup-mul'-reduce x ((y ∷ v) , red) | inr different = refl _
reduced-to-freegroup-mul'-reduce x ((y ′∷ v) , red) = refl _

inv₂ : (a : freegroup) → reduced-to-freegroup (freegroup-to-reduced a) ≡ a
inv₂ = freegroup-rec _
  (refl _)
  (λ x u p → reduced-to-freegroup-mul-reduce x (freegroup-to-reduced u)
             ∘ map (λ t → x · t) {y = u} p)
  (λ x u p → reduced-to-freegroup-mul'-reduce x (freegroup-to-reduced u)
             ∘ map (λ t → x ⁻¹· t) {y = u} p)
  (λ x u t → π₁ (freegroup-is-set _ _ _ _))
  (λ x u t → π₁ (freegroup-is-set _ _ _ _))
  (λ u → is-increasing-hlevel 1 _ (freegroup-is-set _ _))

freegroup-equiv-reduced : freegroup ≃ reduced-word
freegroup-equiv-reduced =
  (freegroup-to-reduced , iso-is-eq _ reduced-to-freegroup inv₁ inv₂)
