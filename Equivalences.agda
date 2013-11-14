{-# OPTIONS --without-K #-}

open import Types
open import Functions
open import Paths
open import HLevel

module Equivalences where

hfiber : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) (y : B) → Set (max i j)
hfiber {A = A} f y = Σ A (λ x → f x ≡ y)

is-equiv : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (max i j)
is-equiv {B = B} f = (y : B) → is-contr (hfiber f y)

_~_ : ∀ {i j} {A : Set i} {B : Set j} (f g : A → B) → Set (max i j)
_~_ {A = A} f g = (x : A) → (f x ≡ g x)

qinv : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (max i j)
qinv {A = A} {B = B} f = Σ (B → A) (λ g → ((f ◯ g) ~ id B) × ((g ◯ f) ~ id A))

is-hae : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (max i j)
is-hae {A = A} {B = B} f =
  Σ (B → A)          (λ g →
  Σ ((g ◯ f) ~ id A) (λ η → 
  Σ ((f ◯ g) ~ id B) (λ ε →
  (x : A) → ap f (η x) ≡ ε (f x)))) 

qinv-to-hae : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → qinv f → is-hae f
qinv-to-hae {A = A} {B = B} f (g , (ε , η)) = g , (η , (ε' , τ)) where
  ε' : (f ◯ g) ~ id B
  ε' b = ! (ε (f (g b))) ∘ ap f (η (g b)) ∘ ε b

  lem : (a : A) → η (g (f a)) ≡ ap (g ◯ f) (η a)
  lem a =
      η (g (f a))
    ≡⟨ ! (refl-right-unit (η (g (f a))) ) ⟩
      η (g (f a)) ∘ refl
    ≡⟨ ap (λ p → η (g (f a)) ∘ p) (! (opposite-right-inverse (η a))) ⟩
      η (g (f a)) ∘ (η a ∘ (! (η a)))
    ≡⟨ ! (concat-assoc (η (g (f a))) (η a) (! (η a))) ⟩
      (η (g (f a)) ∘ η a) ∘ (! (η a))
    ≡⟨ ap (λ p → p ∘ (! (η a)) ) (! (homotopy-naturality-toid (g ◯ f) η (η a))) ⟩ 
      (ap (g ◯ f) (η a) ∘ η a) ∘ (! (η a))
    ≡⟨ concat-assoc (ap (g ◯ f) (η a)) (η a) (! (η a)) ⟩
      ap (g ◯ f) (η a) ∘ (η a ∘ (! (η a)))
    ≡⟨ ap (λ p → ap (g ◯ f) (η a) ∘ p) (opposite-right-inverse (η a)) ⟩
      ap (g ◯ f) (η a) ∘ refl
    ≡⟨ refl-right-unit (ap (g ◯ f) (η a)) ⟩
      ap (g ◯ f) (η a)
    ∎

  lem₂ : (a : A) →  ε (f (g (f a))) ∘ ap f (η a) ≡ ap f (η (g (f a))) ∘ ε (f a)
  lem₂ a =
    ! (ap f (η (g (f a))) ∘ ε (f a)
    ≡⟨ ap (λ p → ap f p ∘ ε (f a)) (lem a) ⟩
      ap f (ap (g ◯ f) (η a)) ∘ ε (f a)
    ≡⟨ ap (λ p → p ∘ ε (f a)) (compose-ap f (g ◯ f) (η a)) ⟩
      ap (f ◯ (g ◯ f)) (η a) ∘ ε (f a)
    ≡⟨ homotopy-naturality (f ◯ (g ◯ f)) f (λ x → ε (f x)) (η a) ⟩
      ε (f (g (f a))) ∘ ap f (η a)
    ∎)

  τ : (a : A) → ap f (η a) ≡ ε' (f a)
  τ a = 
      ap f (η a)
    ≡⟨ refl ⟩
      refl ∘ ap f (η a)
    ≡⟨ ap (λ p → p ∘ ap f (η a)) (! (opposite-left-inverse (ε (f (g (f a)))))) ⟩
      (! (ε (f (g (f a)))) ∘ (ε (f (g (f a))))) ∘ ap f (η a)
    ≡⟨ concat-assoc (! (ε (f (g (f a))))) (ε (f (g (f a)))) (ap f (η a)) ⟩
      ! (ε (f (g (f a)))) ∘ ((ε (f (g (f a)))) ∘ ap f (η a))
    ≡⟨ ap (λ p → ! (ε (f (g (f a)))) ∘ p) (lem₂ a) ⟩
       ! (ε (f (g (f a)))) ∘ (ap f (η (g (f a))) ∘ ε (f a))
    ∎

hae-is-equiv : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → is-hae f → is-equiv f
hae-is-equiv f (g , (η , (ε , τ))) y = (g y , ε y) , contr where
  contr : (xp : hfiber f y) → xp ≡ g y , ε y
  contr (x , p) = total-Σ-eq ( ((! (η x)) ∘ ap g p) , t) where
    t : transport (λ z → f z ≡ y) (! (η x) ∘ ap g p) p ≡ ε y
    t =
        transport (λ z → f z ≡ y) (! (η x) ∘ ap g p) p
      ≡⟨ trans-app≡cst f y (! (η x) ∘ ap g p) p ⟩
        ! (ap f (! (η x) ∘ ap g p)) ∘ p
      ≡⟨ ap (λ q → q ∘ p) (opposite-ap f (! (η x) ∘ ap g p)) ⟩
        ap f (! (! (η x) ∘ ap g p)) ∘ p
      ≡⟨ ap (λ q → ap f q ∘ p) (opposite-concat (! (η x)) (ap g p)) ⟩
        ap f (! (ap g p) ∘ ! (! (η x))) ∘ p
      ≡⟨ ap (λ q → ap f (! (ap g p) ∘ q) ∘ p) (opposite-opposite (η x)) ⟩
        ap f (! (ap g p) ∘ η x) ∘ p
      ≡⟨ ap (λ q → q ∘ p) (ap-concat f (! (ap g p)) (η x)) ⟩
        (ap f (! (ap g p)) ∘ ap f (η x)) ∘ p
      ≡⟨ ap (λ q → (q ∘ ap f (η x)) ∘ p) (ap-opposite f (ap g p)) ⟩
        (! (ap f (ap g p)) ∘ ap f (η x)) ∘ p
      ≡⟨ ap (λ q → (! q ∘ ap f (η x)) ∘ p) (compose-ap f g p) ⟩
        (! (ap (f ◯ g) p) ∘ ap f (η x)) ∘ p
      ≡⟨ ap (λ q → ((! (ap (f ◯ g) p)) ∘ q) ∘ p ) (τ x) ⟩
        (! (ap (f ◯ g) p) ∘ ε (f x)) ∘ p
      ≡⟨ ap (λ q → (q ∘ ε (f x)) ∘ p) (opposite-ap (f ◯ g) p) ⟩
        (ap (f ◯ g) (! p) ∘ ε (f x)) ∘ p
      ≡⟨ ap (λ q → q ∘ p) (homotopy-naturality-toid (f ◯ g) ε (! p)) ⟩ 
        (ε y ∘ ! p) ∘ p
      ≡⟨ concat-assoc (ε y) (! p) p ⟩ 
        ε y ∘ ((! p) ∘ p)
      ≡⟨ ap (λ q → ε y ∘ q) (opposite-left-inverse p) ⟩ 
        ε y ∘ refl
      ≡⟨ refl-right-unit (ε y) ⟩
        ε y
      ∎

_≃_ : ∀ {i j} (A : Set i) (B : Set j) → Set (max i j)  -- \simeq
A ≃ B = Σ (A → B) is-equiv

id-is-equiv : ∀ {i} (A : Set i) → is-equiv (id A)
id-is-equiv A = pathto-is-contr

id-equiv : ∀ {i} (A : Set i) → A ≃ A
id-equiv A = (id A , id-is-equiv A)

path-to-eq : ∀ {i} {A B : Set i} → (A ≡ B → A ≃ B)
path-to-eq refl = id-equiv _

module _ {i} {j} {A : Set i} {B : Set j} where

  -- Notation for the application of an equivalence to an argument
  _☆_ : (f : A ≃ B) (x : A) → B
  f ☆ x = (π₁ f) x

  inverse : (f : A ≃ B) → B → A
  inverse (f , e) = λ y → π₁ (π₁ (e y))

  abstract
    inverse-right-inverse : (f : A ≃ B) (y : B) → f ☆ (inverse f y) ≡ y
    inverse-right-inverse (f , e) y = π₂ (π₁ (e y))

    inverse-left-inverse : (f : A ≃ B) (x : A) → inverse f (f ☆ x) ≡ x
    inverse-left-inverse (f , e) x =
      ! (base-path (π₂ (e (f x)) (x , refl)))

    hfiber-triangle : (f : A → B) (z : B) {x y : hfiber f z} (p : x ≡ y)
      → ap f (base-path p) ∘ π₂ y ≡ π₂ x
    hfiber-triangle f z {x} {.x} refl = refl

    inverse-triangle : (f : A ≃ B) (x : A) →
      inverse-right-inverse f (f ☆ x) ≡ ap (π₁ f) (inverse-left-inverse f x)
    inverse-triangle (f , e) x = move1!-left-on-left _ _
      (hfiber-triangle f _ (π₂ (e (f x)) (x , refl)))
       ∘ opposite-ap f _

  -- Needs to be completely rewritten
  adjiso-is-eq : (f : A → B) (g : B → A) (h : (y : B) → f (g y) ≡ y)
    (h' : (x : A) → g (f x) ≡ x) (adj : (x : A) → ap f (h' x) ≡ h (f x))
    → is-equiv f
  adjiso-is-eq f g h h' adj y = ((g y , h y), path) where
    abstract
      path : ∀ (fiber : hfiber f y) → fiber ≡ (g y , h y)
      path = λ y' → Σ-eq (! (h' (π₁ y')) ∘ ap g (π₂ y'))
        (trans-app≡cst f _ (! (h' (π₁ y')) ∘ ap g (π₂ y')) (π₂ y') ∘
        move-right-on-right (! (ap f (! (h' (π₁ y')) ∘ ap g (π₂ y'))))
          (π₂ y') (h y)
          (ap ! (ap-concat f (! (h' (π₁ y'))) (ap g (π₂ y')))
          ∘ (opposite-concat (ap f (! (h' (π₁ y')))) (ap f (ap g (π₂ y'))) ∘
              (whisker-left (! (ap f (ap g (π₂ y'))))
                (opposite-ap f (! (h' (π₁ y')))
                ∘ ap (ap f) (opposite-opposite (h' (π₁ y'))))
         ∘ ((whisker-left (! (ap f (ap g (π₂ y')))) (adj (π₁ y'))
         ∘ whisker-right (h (f (π₁ y'))) (ap ! (compose-ap f g (π₂ y'))
                                         ∘ opposite-ap (f ◯ g) (π₂ y')))
         ∘ homotopy-naturality-toid (f ◯ g) h (! (π₂ y')))))))

  abstract
    -- Needs to be completely rewritten
    iso-is-adjiso : (f : A → B) (g : B → A) (h : (y : B) → f (g y) ≡ y)
      (h' : (x : A) → g (f x) ≡ x)
      → Σ ((x : A) → g (f x) ≡ x) (λ h'' → (x : A) → ap f (h'' x) ≡ h (f x))
    iso-is-adjiso f g h h' = ((λ x → ! (ap g (ap f (h' x)))
                                     ∘ (ap g (h (f x)) ∘ h' x)) ,
      (λ x → ap-concat f (! (ap g (ap f (h' x)))) (ap g (h (f x)) ∘ h' x)
           ∘ (whisker-right (ap f (ap g (h (f x)) ∘ h' x))
                            (ap-opposite f (ap g (ap f (h' x))))
           ∘ move!-right-on-left (ap f (ap g (ap f (h' x))))
                                 (ap f (ap g (h (f x)) ∘ h' x)) (h (f x))
             (ap-concat f (ap g (h (f x))) (h' x)
           ∘ (whisker-right (ap f (h' x)) (compose-ap f g (h (f x)))
           ∘ ((whisker-right (ap f (h' x)) {q = ap (f ◯ g) (h (f x))}
                 {r = h (f (g (f x)))} (anti-whisker-right (h (f x))
             (homotopy-naturality-toid (f ◯ g) h (h (f x))))
           ∘ ! (homotopy-naturality-toid (f ◯ g) h (ap f (h' x))))
           ∘ whisker-right (h (f x)) (ap-compose f g (ap f (h' x)))))))))

  iso-is-eq : (f : A → B) (g : B → A) (h : (y : B) → f (g y) ≡ y)
    (h' : (x : A) → g (f x) ≡ x) → is-equiv f
  iso-is-eq f g h h' = adjiso-is-eq f g h (π₁ (iso-is-adjiso f g h h'))
    (π₂ (iso-is-adjiso f g h h'))

  -- When using [iso-is-eq], the other map which is given is an inverse
  inverse-iso-is-eq : (f : A → B) (g : B → A) (h : (y : B) → f (g y) ≡ y)
    (h' : (x : A) → g (f x) ≡ x) → inverse (f , iso-is-eq f g h h') ≡ g
  inverse-iso-is-eq f g h h' = refl

-- The inverse of an equivalence is an equivalence
inverse-is-equiv : ∀ {i} {j} {A : Set i} {B : Set j} (f : A ≃ B)
  → is-equiv (inverse f)
inverse-is-equiv f = iso-is-eq _ (π₁ f) (inverse-left-inverse f)
                                        (inverse-right-inverse f)


_⁻¹ : ∀ {i} {j} {A : Set i} {B : Set j} (f : A ≃ B) → B ≃ A  -- \^-\^1
_⁻¹ f = (inverse f , inverse-is-equiv f)

-- Equivalences are injective
equiv-is-inj : ∀ {i} {j} {A : Set i} {B : Set j} (f : A ≃ B) (x y : A)
  → (f ☆ x ≡ f ☆ y → x ≡ y)
equiv-is-inj f x y p = ! (inverse-left-inverse f x)
                       ∘ (ap (inverse f) p ∘ inverse-left-inverse f y)

-- Any contractible type is equivalent to the unit type
contr-equiv-unit : ∀ {i j} {A : Set i} → (is-contr A → A ≃ unit {j})
contr-equiv-unit e = ((λ _ → tt) , iso-is-eq _ (λ _ → π₁ e) (λ y → refl)
                                             (λ x → ! (π₂ e x)))

-- The composite of two equivalences is an equivalence
compose-is-equiv : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k}
  (f : A ≃ B) (g : B ≃ C) → is-equiv (π₁ g ◯ π₁ f)
compose-is-equiv f g =
  iso-is-eq _ (inverse f ◯ inverse g)
    (λ y → ap (π₁ g) (inverse-right-inverse f (inverse g y))
           ∘ inverse-right-inverse g y)
    (λ x → ap (inverse f) (inverse-left-inverse g (π₁ f x))
           ∘ inverse-left-inverse f x)

equiv-compose : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k}
  → (A ≃ B → B ≃ C → A ≃ C)
equiv-compose f g = ((π₁ g ◯ π₁ f) , compose-is-equiv f g)

-- An equivalence induces an equivalence on the path spaces
-- The proofs here can probably be simplified
module _ {i j} {A : Set i} {B : Set j} (f : A ≃ B) (x y : A) where

  private
    ap-is-inj : (p : f ☆ x ≡ f ☆ y) → x ≡ y
    ap-is-inj p = equiv-is-inj f x y p

    abstract
      left-inverse : (p : x ≡ y) → ap-is-inj (ap (π₁ f) p) ≡ p
      left-inverse p =
        move!-right-on-left (inverse-left-inverse f x) _ p
          (move-right-on-right (ap (inverse f) (ap (π₁ f) p)) _ _
           (compose-ap (inverse f) (π₁ f) p
           ∘ move!-left-on-right (ap (inverse f ◯ π₁ f) p)
               (inverse-left-inverse f x ∘ p)
               (inverse-left-inverse f y)
               (homotopy-naturality-toid (inverse f ◯ π₁ f)
                 (inverse-left-inverse f) p)))

      right-inverse : (p : f ☆ x ≡ f ☆ y) → ap (π₁ f) (ap-is-inj p) ≡ p
      right-inverse p =
        ap-concat (π₁ f) (! (inverse-left-inverse f x)) _
        ∘ (ap (λ u → u ∘ ap (π₁ f) (ap (inverse f) p
                  ∘ inverse-left-inverse f y))
               (ap-opposite (π₁ f) (inverse-left-inverse f x))
          ∘ move!-right-on-left (ap (π₁ f) (inverse-left-inverse f x)) _ p
            (ap-concat (π₁ f) (ap (inverse f) p) (inverse-left-inverse f y)
            ∘ (ap (λ u → u ∘ ap (π₁ f) (inverse-left-inverse f y))
                   (compose-ap (π₁ f) (inverse f) p)
            ∘ (whisker-left (ap (π₁ f ◯ inverse f) p)
                            (! (inverse-triangle f y))
            ∘ (homotopy-naturality-toid (π₁ f ◯ inverse f)
                                        (inverse-right-inverse f)
                                        p
            ∘ whisker-right p (inverse-triangle f x))))))

  equiv-ap : (x ≡ y) ≃ (f ☆ x ≡ f ☆ y)
  equiv-ap = (ap (π₁ f) , iso-is-eq _ ap-is-inj right-inverse left-inverse)

abstract
  total-Σ-eq-is-equiv : ∀ {i j} {A : Set i} {P : A → Set j} {x y : Σ A P}
    → is-equiv (total-Σ-eq {xu = x} {yv = y})
  total-Σ-eq-is-equiv {P = P} = iso-is-eq _
    (λ totp → (base-path totp , fiber-path totp))
    Σ-eq-base-path-fiber-path
    (λ p → Σ-eq (base-path-Σ-eq (π₁ p) (π₂ p))
                      (fiber-path-Σ-eq {P = P} (π₁ p) (π₂ p)))

total-Σ-eq-equiv : ∀ {i j} {A : Set i} {P : A → Set j} {x y : Σ A P}
  → (Σ (π₁ x ≡ π₁ y) (λ p → transport P p (π₂ x) ≡ (π₂ y))) ≃ (x ≡ y)
total-Σ-eq-equiv = (total-Σ-eq , total-Σ-eq-is-equiv)
