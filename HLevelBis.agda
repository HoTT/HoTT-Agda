{-# OPTIONS --without-K #-}

open import Types
open import Functions
open import Paths
open import HLevel
open import Equivalences
open import Univalence
open import Funext

module HLevelBis where

abstract
  -- Every map between contractible types is an equivalence
  contr-to-contr-is-equiv : ∀ {i j} {A : Set i} {B : Set j} (f : A → B)
    → (is-contr A → is-contr B → is-equiv f)
  contr-to-contr-is-equiv f cA cB y =
    ((π₁ cA , (contr-has-all-paths cB _ _))
    , (λ _ → Σ-eq (contr-has-all-paths cA _ _)
                        (contr-has-all-paths (≡-is-hlevel 0 cB) _ _)))

  is-contr-is-prop : ∀ {i} {A : Set i} → is-prop (is-contr A)
  is-contr-is-prop {A = A} = all-paths-is-prop
    (λ x y → Σ-eq (π₂ y (π₁ x))
                        (funext (lemma x y (π₂ y (π₁ x))))) where

    lemma : (x y : is-contr A) (p : π₁ x ≡ π₁ y) (t : A)
      → transport (λ v → (z : A) → z ≡ v) p (π₂ x) t ≡ π₂ y t
    lemma (x , p) (.x , q) (refl .x) t = contr-has-all-paths
                                         (≡-is-hlevel 0 (x , p)) _ _

  -- Equivalent types have the same h-level
  equiv-types-hlevel : ∀ {i j} {A : Set i} {B : Set j} (n : ℕ) (f : A ≃ B)
    → (is-hlevel n A → is-hlevel n B)
  equiv-types-hlevel O (f , e) (x , p) =
    (f x , (λ y → ! (inverse-right-inverse (f , e) y) ∘ map f (p _)))
  equiv-types-hlevel (S n) f c = λ x y →
    equiv-types-hlevel n (equiv-map (f ⁻¹) x y ⁻¹) (c (f ⁻¹ ☆ x) (f ⁻¹ ☆ y))

  Π-is-hlevel : ∀ {i j} (n : ℕ) {A : Set i} {P : A → Set j}
    → (((x : A) → is-hlevel n (P x)) → is-hlevel n (Π A P))
  Π-is-hlevel O p = ((λ x → π₁ (p x)) , (λ f → funext (λ x → π₂ (p x) (f x))))
  Π-is-hlevel 1 p =
    all-paths-is-prop (λ f g → funext (λ x → π₁ (p x (f x) (g x))))
  Π-is-hlevel (S n) p = λ f g →
    equiv-types-hlevel n funext-equiv (Π-is-hlevel n (λ x → p x (f x) (g x)))

  →-is-hlevel : ∀ {i j} (n : ℕ) {A : Set i} {B : Set j}
    → (is-hlevel n B → is-hlevel n (A → B))
  →-is-hlevel n p = Π-is-hlevel n (λ _ → p)

  is-hlevel-is-prop : ∀ {i} (n : ℕ) {A : Set i} → is-prop (is-hlevel n A)
  is-hlevel-is-prop O = is-contr-is-prop
  is-hlevel-is-prop (S n) =
    Π-is-hlevel 1 (λ x → Π-is-hlevel 1 (λ y → is-hlevel-is-prop n))

  Σ-is-hlevel : ∀ {i j} (n : ℕ) {A : Set i} {P : A → Set j}
    → (is-hlevel n A → ((x : A) → is-hlevel n (P x)) → is-hlevel n (Σ A P))
  Σ-is-hlevel O p q = ((π₁ p , (π₁ (q (π₁ p)))) ,
                       (λ y → Σ-eq (π₂ p _) (π₂ (q _) _)))
  Σ-is-hlevel (S n) p q =
    λ x y → equiv-types-hlevel n total-Σ-eq-equiv
                               (Σ-is-hlevel n (p _ _) (λ _ → q _ _ _))

  ×-is-hlevel : ∀ {i j} (n : ℕ) {A : Set i} {B : Set j}
    → (is-hlevel n A → is-hlevel n B → is-hlevel n (A × B))
  ×-is-hlevel n pA pB = Σ-is-hlevel n pA (λ x → pB)

  subtype-hlevel-S-is-hlevel-S : ∀ {i j} {A : Set i} {P : A → Set j} (n : ℕ)
    → (is-hlevel (S n) A → ((x : A) → is-prop (P x)) → is-hlevel (S n) (Σ A P))
  subtype-hlevel-S-is-hlevel-S n p q =
    Σ-is-hlevel (S n) p (λ x → prop-is-hlevel-S n (q x))

  is-equiv-is-prop : ∀ {i j} {A : Set i} {B : Set j} (f : A → B)
    → is-prop (is-equiv f)
  is-equiv-is-prop f = Π-is-hlevel 1 (λ x → is-contr-is-prop)

-- Type of all types of some h-level

hLevel : (n : ℕ) (i : Level) → Set (suc i)
hLevel n i = Σ (Set i) (is-hlevel n)

hProp : (i : Level) → Set (suc i)
hProp i = hLevel 1 i

hSet : (i : Level) → Set (suc i)
hSet i = hLevel 2 i

-- [hLevel n] is of h-level [S n]

abstract
  ≃-is-hlevel : ∀ {i} (n : ℕ) {A B : Set i}
    → (is-hlevel n A → is-hlevel n B → is-hlevel n (A ≃ B))
  ≃-is-hlevel 0 pA pB =
    (((λ _ → π₁ pB) , contr-to-contr-is-equiv _ pA pB)
    , (λ _ → Σ-eq (funext (λ _ → contr-has-all-paths pB _ _))
                        (π₁ (is-equiv-is-prop _ _ _))))
  ≃-is-hlevel (S n) pA pB = Σ-is-hlevel (S n) (→-is-hlevel (S n) pB)
                                      (λ _ → prop-is-hlevel-S n
                                             (is-equiv-is-prop _))

  hLevel-is-hlevel : (n : ℕ) (i : Level) → is-hlevel (S n) (hLevel n i)
  hLevel-is-hlevel n i A B =
    equiv-types-hlevel n total-Σ-eq-equiv
    (Σ-is-hlevel n (equiv-types-hlevel n eq-to-path-equiv
                                      (≃-is-hlevel n (π₂ A) (π₂ B)))
    (λ _ → contr-is-hlevel n (≡-is-hlevel 0
           (inhab-prop-is-contr (π₂ B) (is-hlevel-is-prop n {-(π₁ B)-})))))

  hProp-is-set : (i : Level) → is-set (hProp i)
  hProp-is-set i = hLevel-is-hlevel 1 i

  hSet-is-gpd : (i : Level) → is-gpd (hSet i)
  hSet-is-gpd i = hLevel-is-hlevel 2 i
