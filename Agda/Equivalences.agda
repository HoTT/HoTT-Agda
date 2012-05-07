{-# OPTIONS --without-K #-}

open import Types
open import Functions
open import Paths
open import Contractible

module Equivalences where

hfiber : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) (y : B) → Set (max i j)
hfiber {A = A} f y = Σ A (λ x → f x ≡ y)

is-equiv : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (max i j)
is-equiv {B = B} f = (y : B) → is-contr (hfiber f y)

_≃_ : ∀ {i j} (A : Set i) (B : Set j) → Set (max i j)  -- \simeq
A ≃ B = Σ (A → B) is-equiv

-- Notation for the application of an equivalence to an argument

infix 1 _$_

_$_ : ∀ {i j} {A : Set i} {B : Set j} (f : A ≃ B) (x : A) → B
f $ x = (π₁ f) x

inverse : ∀ {i j} {A : Set i} {B : Set j} (f : A ≃ B) → B → A
inverse (f , e) y = π₁ (π₁ (e y))

inverse-right-inverse : ∀ {i j} {A : Set i} {B : Set j} (f : A ≃ B) (y : B) → (f $ ((inverse f) y)) ≡ y
inverse-right-inverse (f , e) y = π₂ (π₁ (e y))

inverse-left-inverse : ∀ {i j} {A : Set i} {B : Set j} (f : A ≃ B) (x : A) → (inverse f) (f $ x) ≡ x
inverse-left-inverse (f , e) x = ! (base-path (π₂ (e (f x)) (x , refl (f x))))

hfiber-triangle : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) (z : B) {x y : hfiber f z} (p : x ≡ y) → map f (base-path p) ∘ (π₂ y) ≡ π₂ x
hfiber-triangle f z (refl _) = refl _

inverse-triangle : ∀ {i j} {A : Set i} {B : Set j} (f : A ≃ B) (x : A) →
  inverse-right-inverse f (f $ x) ≡ map (π₁ f) (inverse-left-inverse f x)
inverse-triangle f x = move1!-left-on-left _ _ (hfiber-triangle (π₁ f) _ (π₂ (π₂ f (f $ x)) (x , refl (π₁ f x)))) ∘ opposite-map (π₁ f) _

equiv-is-inj : ∀ {i j} {A : Set i} {B : Set j} (f : A ≃ B) (x y : A) (p : (f $ x) ≡ (f $ y)) → x ≡ y
equiv-is-inj f x y p = ! (inverse-left-inverse f x) ∘ (map (inverse f) p ∘ inverse-left-inverse f y)

abstract
  adjiso-is-eq : ∀ {i j} {A : Set i} {B : Set j}
    (f : A → B) (g : B → A) (h : (y : B) → f (g y) ≡ y) (h' : (x : A) → g (f x) ≡ x) (adj : (x : A) → map f (h' x) ≡ h (f x)) → is-equiv f
  adjiso-is-eq f g h h' adj = λ y → ((g y , h y) , (λ y' → total-path (! (h' (π₁ y')) ∘ map g (π₂ y'))
    (trans-fx≡a f _ (! (h' (π₁ y')) ∘ map g (π₂ y')) (π₂ y') ∘
      move-right-on-right (! (map f (! (h' (π₁ y')) ∘ map g (π₂ y')))) (π₂ y') (h y)
       (map ! (map-concat f (! (h' (π₁ y'))) (map g (π₂ y')))
       ∘ (opposite-concat (map f (! (h' (π₁ y')))) (map f (map g (π₂ y'))) ∘
            (whisker-left (! (map f (map g (π₂ y')))) (opposite-map f (! (h' (π₁ y'))) ∘ map (map f) (opposite-opposite (h' (π₁ y'))))
       ∘ ((whisker-left (! (map f (map g (π₂ y')))) (adj (π₁ y'))
       ∘ whisker-right (h (f (π₁ y'))) (map ! (compose-map f g (π₂ y')) ∘ opposite-map (f ◯ g) (π₂ y')))
       ∘ homotopy-naturality-toid (f ◯ g) h (! (π₂ y')))))))))

abstract 
  iso-is-adjiso : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) (g : B → A) (h : (y : B) → f (g y) ≡ y) (h' : (x : A) → g (f x) ≡ x)
    → Σ ((x : A) → g (f x) ≡ x) (λ h'' → (x : A) → map f (h'' x) ≡ h (f x))
  iso-is-adjiso f g h h' = ((λ x → ! (map g (map f (h' x))) ∘ (map g (h (f x)) ∘ h' x)) ,
    (λ x → map-concat f (! (map g (map f (h' x)))) (map g (h (f x)) ∘ h' x)
         ∘ (whisker-right (map f (map g (h (f x)) ∘ h' x)) (map-opposite f (map g (map f (h' x))))
         ∘ move!-right-on-left (map f (map g (map f (h' x)))) (map f (map g (h (f x)) ∘ h' x)) (h (f x))
           (map-concat f (map g (h (f x))) (h' x)
         ∘ (whisker-right (map f (h' x)) (compose-map f g (h (f x)))
         ∘ ((whisker-right (map f (h' x)) {q = map (f ◯ g) (h (f x))}
               {r = h (f (g (f x)))} (anti-whisker-right (h (f x))
           (homotopy-naturality-toid (f ◯ g) h (h (f x))))
         ∘ ! (homotopy-naturality-toid (f ◯ g) h (map f (h' x))))
         ∘ whisker-right (h (f x)) (map-compose f g (map f (h' x)))))))))

abstract
  iso-is-eq : ∀ {i j} {A : Set i} {B : Set j}
    (f : A → B) (g : B → A) (h : (y : B) → f (g y) ≡ y) (h' : (x : A) → g (f x) ≡ x) → is-equiv f
  iso-is-eq f g h h' = adjiso-is-eq f g h (π₁ (iso-is-adjiso f g h h')) (π₂ (iso-is-adjiso f g h h'))

-- The inverse of an equivalence is an equivalence

inverse-is-equiv : ∀ {i j} {A : Set i} {B : Set j} (f : A ≃ B) → is-equiv (inverse f)
inverse-is-equiv f = iso-is-eq _ (π₁ f) (inverse-left-inverse f) (inverse-right-inverse f)

_⁻¹ : ∀ {i j} {A : Set i} {B : Set j} (f : A ≃ B) → B ≃ A  -- \^-\^1
_⁻¹ f = (inverse f , inverse-is-equiv f)

-- Any contractible type is equivalent to the unit type
contr-equiv-unit : ∀ {i j} {A : Set i} (e : is-contr A) → A ≃ unit {j}
contr-equiv-unit e = ((λ _ → tt) , iso-is-eq _ (λ _ → π₁ e) (λ y → refl tt) (λ x → ! (π₂ e x)))

-- An equivalence induces an equivalence on the path spaces
module MapEquiv {i j} {A : Set i} {B : Set j} (f : A ≃ B) (x y : A) where

  map-inverse : (p : (f $ x) ≡ (f $ y)) → x ≡ y
  map-inverse p = equiv-is-inj f x y p

  left-inverse : (p : x ≡ y) → map-inverse (map (π₁ f) p) ≡ p
  left-inverse p = move!-right-on-left (inverse-left-inverse f x) _ p
                      (move-right-on-right (map (inverse f) (map (π₁ f) p)) _ _
                       (compose-map (inverse f) (π₁ f) p ∘ move!-left-on-right (map (inverse f ◯ π₁ f) p)
                                                             (inverse-left-inverse f x ∘ p) (inverse-left-inverse f y)
                                                               (homotopy-naturality-toid (inverse f ◯ π₁ f) (inverse-left-inverse f) p)))

  right-inverse : (p : (f $ x) ≡ (f $ y)) → map (π₁ f) (map-inverse p) ≡ p
  right-inverse p = map-concat (π₁ f) (! (inverse-left-inverse f x)) _
                ∘ (map
                    (λ u →
                       u ∘ map (π₁ f) (map (inverse f) p ∘ inverse-left-inverse f y))
                    (map-opposite (π₁ f) (inverse-left-inverse f x))
                    ∘ move!-right-on-left (map (π₁ f) (inverse-left-inverse f x)) _ p
                      (map-concat (π₁ f) (map (inverse f) p) (inverse-left-inverse f y) ∘
                        (map (λ u → u ∘ map (π₁ f) (inverse-left-inverse f y))
                           (compose-map (π₁ f) (inverse f) p)
                           ∘ (whisker-left (map (π₁ f ◯ inverse f) p) (! (inverse-triangle f y))
                                ∘ (homotopy-naturality-toid (π₁ f ◯ inverse f)
                                     (inverse-right-inverse f) p
                                     ∘ whisker-right p (inverse-triangle f x))))))

  equiv-map : ((x ≡ y) ≃ ((f $ x) ≡ (f $ y)))
  equiv-map = (map (π₁ f) , iso-is-eq _ map-inverse right-inverse left-inverse)

equiv-map : ∀ {i j} {A : Set i} {B : Set j} (f : A ≃ B) (x y : A) → ((x ≡ y) ≃ ((f $ x) ≡ (f $ y)))
equiv-map f x y = MapEquiv.equiv-map f x y