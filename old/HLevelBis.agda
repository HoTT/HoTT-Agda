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
                        (contr-has-all-paths (≡-is-truncated _ cB) _ _)))

  is-contr-is-prop : ∀ {i} {A : Set i} → is-prop (is-contr A)
  is-contr-is-prop {A = A} = all-paths-is-prop
    (λ x y → Σ-eq (π₂ y (π₁ x))
                        (funext (lemma x y (π₂ y (π₁ x))))) where

    lemma : (x y : is-contr A) (p : π₁ x ≡ π₁ y) (t : A)
      → transport (λ v → (z : A) → z ≡ v) p (π₂ x) t ≡ π₂ y t
    lemma (x , p) (.x , q) refl t = contr-has-all-paths
                                    (≡-is-truncated _ (x , p)) _ _

  -- Equivalent types have the same truncation level
  equiv-types-truncated : ∀ {i j} {A : Set i} {B : Set j} (n : ℕ₋₂) (f : A ≃ B)
    → (is-truncated n A → is-truncated n B)
  equiv-types-truncated ⟨-2⟩ (f , e) (x , p) =
    (f x , (λ y → ! (inverse-right-inverse (f , e) y) ∘ ap f (p _)))
  equiv-types-truncated (S n) f c = λ x y →
    equiv-types-truncated n (equiv-ap (f ⁻¹) x y ⁻¹) (c (f ⁻¹ ☆ x) (f ⁻¹ ☆ y))

  Π-is-truncated : ∀ {i j} (n : ℕ₋₂) {A : Set i} {P : A → Set j}
    → (((x : A) → is-truncated n (P x)) → is-truncated n (Π A P))
  Π-is-truncated ⟨-2⟩ p =
    ((λ x → π₁ (p x)) , (λ f → funext (λ x → π₂ (p x) (f x))))
  Π-is-truncated (S n) p = λ f g →
    equiv-types-truncated n funext-equiv
      (Π-is-truncated n (λ x → p x (f x) (g x)))

  →-is-truncated : ∀ {i j} (n : ℕ₋₂) {A : Set i} {B : Set j}
    → (is-truncated n B → is-truncated n (A → B))
  →-is-truncated n p = Π-is-truncated n (λ _ → p)

  is-truncated-is-prop : ∀ {i} (n : ℕ₋₂) {A : Set i}
    → is-prop (is-truncated n A)
  is-truncated-is-prop ⟨-2⟩ = is-contr-is-prop
  is-truncated-is-prop (S n) =
    Π-is-truncated _ (λ x → Π-is-truncated _ (λ y → is-truncated-is-prop n))

  is-set-is-prop : ∀ {i} {A : Set i} → is-prop (is-set A)
  is-set-is-prop = is-truncated-is-prop ⟨0⟩

  Σ-is-truncated : ∀ {i j} (n : ℕ₋₂) {A : Set i} {P : A → Set j}
    → (is-truncated n A → ((x : A) → is-truncated n (P x))
      → is-truncated n (Σ A P))
  Σ-is-truncated ⟨-2⟩ p q = ((π₁ p , (π₁ (q (π₁ p)))) ,
                       (λ y → Σ-eq (π₂ p _) (π₂ (q _) _)))
  Σ-is-truncated (S n) p q =
    λ x y → equiv-types-truncated n total-Σ-eq-equiv
                               (Σ-is-truncated n (p _ _) (λ _ → q _ _ _))

  ×-is-truncated : ∀ {i j} (n : ℕ₋₂) {A : Set i} {B : Set j}
    → (is-truncated n A → is-truncated n B → is-truncated n (A × B))
  ×-is-truncated n pA pB = Σ-is-truncated n pA (λ x → pB)

  subtype-truncated-S-is-truncated-S : ∀ {i j} (n : ℕ₋₂)
    {A : Set i} {P : A → Set j}
    → (is-truncated (S n) A → ((x : A) → is-prop (P x))
      → is-truncated (S n) (Σ A P))
  subtype-truncated-S-is-truncated-S n p q =
    Σ-is-truncated (S n) p (λ x → prop-is-truncated-S n (q x))

  is-equiv-is-prop : ∀ {i j} {A : Set i} {B : Set j} (f : A → B)
    → is-prop (is-equiv f)
  is-equiv-is-prop f = Π-is-truncated _ (λ x → is-contr-is-prop)

-- Specilization
module _ where
  Π-is-prop : ∀ {i j} {A : Set i} {P : A → Set j}
    → (((x : A) → is-prop (P x)) → is-prop (Π A P))
  Π-is-prop = Π-is-truncated ⟨-1⟩

  Π-is-set : ∀ {i j} {A : Set i} {P : A → Set j}
    → (((x : A) → is-set (P x)) → is-set (Π A P))
  Π-is-set = Π-is-truncated ⟨0⟩

  →-is-set : ∀ {i j} {A : Set i} {B : Set j}
    → (is-set B → is-set (A → B))
  →-is-set = →-is-truncated ⟨0⟩

  →-is-prop : ∀ {i j} {A : Set i} {B : Set j}
    → (is-prop B → is-prop (A → B))
  →-is-prop = →-is-truncated ⟨-1⟩

-- Type of all n-truncated types

Type≤ : (n : ℕ₋₂) (i : Level) → Set (suc i)
Type≤ n i = Σ (Set i) (is-truncated n)

hProp : (i : Level) → Set (suc i)
hProp = Type≤ ⟨-1⟩

hSet : (i : Level) → Set (suc i)
hSet = Type≤ ⟨0⟩

-- [Type≤ n] is (n+1)-truncated

abstract
  ≃-is-truncated : ∀ {i} (n : ℕ₋₂) {A B : Set i}
    → (is-truncated n A → is-truncated n B → is-truncated n (A ≃ B))
  ≃-is-truncated ⟨-2⟩ pA pB =
    (((λ _ → π₁ pB) , contr-to-contr-is-equiv _ pA pB)
    , (λ _ → Σ-eq (funext (λ _ → contr-has-all-paths pB _ _))
                        (π₁ (is-equiv-is-prop _ _ _))))
  ≃-is-truncated (S n) pA pB = Σ-is-truncated (S n) (→-is-truncated (S n) pB)
                                      (λ _ → prop-is-truncated-S n
                                             (is-equiv-is-prop _))

  ≃-is-set : ∀ {i} {A B : Set i} → (is-set A → is-set B → is-set (A ≃ B))
  ≃-is-set = ≃-is-truncated ⟨0⟩

  universe-≡-is-truncated : ∀ {i} (n : ℕ₋₂) {A B : Set i}
    → (is-truncated n A → is-truncated n B → is-truncated n (A ≡ B))
  universe-≡-is-truncated n pA pB = equiv-types-truncated n eq-to-path-equiv
    $ ≃-is-truncated n pA pB

  universe-≡-is-set : ∀ {i} {A B : Set i}
    → (is-set A → is-set B → is-set (A ≡ B))
  universe-≡-is-set = universe-≡-is-truncated ⟨0⟩

  Type≤-is-truncated : (n : ℕ₋₂) (i : Level)
    → is-truncated (S n) (Type≤ n i)
  Type≤-is-truncated n i A B =
    equiv-types-truncated n total-Σ-eq-equiv
    (Σ-is-truncated n (universe-≡-is-truncated n (π₂ A) (π₂ B))
    (λ _ → contr-is-truncated n (≡-is-truncated _
           (inhab-prop-is-contr (π₂ B) (is-truncated-is-prop n {-(π₁ B)-})))))

  hProp-is-set : (i : Level) → is-set (hProp i)
  hProp-is-set = Type≤-is-truncated _

  hSet-is-gpd : (i : Level) → is-gpd (hSet i)
  hSet-is-gpd = Type≤-is-truncated _
