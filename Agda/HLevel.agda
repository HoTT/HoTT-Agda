{-# OPTIONS --without-K #-}

open import Types
open import Paths
open import Contractible
open import Equivalences
open import Univalence
open import Funext

module HLevel where

-- Every map between contractible types is an equivalence
contr-contr-equiv : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) (cA : is-contr A) (cB : is-contr B) → is-equiv f
contr-contr-equiv {i} {j} {A} {B} f cA cB = λ y → ((π₁ cA , (is-contr-path B cB _ _)) , (λ y' → total-path (is-contr-path A cA _ _)
  (is-contr-path _ (path-contr-contr B cB _ _) _ _)))

is-hlevel : ∀ {i} (n : ℕ) (A : Set i) → Set i
is-hlevel O A = is-contr A
is-hlevel 1 A = (x y : A) → (x ≡ y)
is-hlevel (S n) A = (x y : A) → (is-hlevel n (x ≡ y))

is-prop : ∀ {i} (A : Set i) → Set _
is-prop = is-hlevel 1

is-set : ∀ {i} (A : Set i) → Set _
is-set = is-hlevel 2

is-gpd : ∀ {i} (A : Set i) → Set _
is-gpd = is-hlevel 3

is-prop-is-contr : ∀ {i} (A : Set i) → is-prop (is-contr A)
is-prop-is-contr A x y = total-path (π₂ y (π₁ x)) (funext-dep _ _
  (λ x' → (trans-A→Pxy A (λ x0 y' → y' ≡ x0) (π₂ y (π₁ x)) (π₂ x) x' ∘ trans-a≡x (π₂ y (π₁ x)) (π₂ x x')) ∘ lemma-is-prop-is-contr _ y (π₂ x x'))) where

  lemma-is-prop-is-contr : ∀ {i} (A : Set i) (c : is-contr A) {x y : A} (p : x ≡ y) → p ∘ π₂ c y ≡ π₂ c x
  lemma-is-prop-is-contr A c (refl _) = refl _

is-prop-pi : ∀ {i j} (A : Set i) (P : A → Set j) (p : (x : A) → is-prop (P x)) → is-prop ((x : A) → P x)
is-prop-pi A P p f g = funext-dep _ _ (λ x → p x (f x) (g x))

private
  lemma1-is-prop-is-prop : ∀ {i} (A : Set i) (c : is-prop A) {x y : A} (p : x ≡ y) → p ∘ c y y ≡ c x y
  lemma1-is-prop-is-prop A c (refl _) = refl _

  -- We apply the previous lemma with [p = c y y]
  lemma2-is-prop-is-prop : ∀ {i} (A : Set i) (c : is-prop A) (y : A) → c y y ≡ refl y
  lemma2-is-prop-is-prop A c y = anti-whisker-left (c y y) (lemma1-is-prop-is-prop A c (c y y) ∘ ! (refl-right-unit _))

  -- We combine the two lemmas
  lemma3-is-prop-is-prop : ∀ {i} (A : Set i) (c : is-prop A) {x y : A} (p : x ≡ y) → p ≡ c x y
  lemma3-is-prop-is-prop A c (refl _) = ! (lemma2-is-prop-is-prop A c _)

is-prop-is-prop : ∀ {i} (A : Set i) → is-prop (is-prop A)
is-prop-is-prop A c c' = funext-dep _ _ (λ x → funext-dep _ _ (λ x' → lemma3-is-prop-is-prop _ c' (c x x')))

-- Usual definition of [is-prop]
usual-is-prop : ∀ {i} (A : Set i) (c : is-prop A) → ((x y : A) → (is-contr (x ≡ y)))
usual-is-prop A c x y = (c x y , lemma3-is-prop-is-prop A c)

is-prop-hlevel : ∀ {i} (n : ℕ) (A : Set i) → is-prop (is-hlevel n A)
is-prop-hlevel O A = is-prop-is-contr A
is-prop-hlevel (S O) A = is-prop-is-prop A
is-prop-hlevel (S (S n)) A = is-prop-pi _ _ (λ x → is-prop-pi _ _ (λ x' → is-prop-hlevel (S n) (x ≡ x')))

is-increasing-hlevel : ∀ {i} (n : ℕ) (A : Set i) → is-hlevel n A → is-hlevel (S n) A
is-increasing-hlevel O A p = λ x y → π₂ p x ∘ ! (π₂ p y)
is-increasing-hlevel (S O) A p = λ x y → is-increasing-hlevel O (x ≡ y) (p x y , lemma3-is-prop-is-prop A p)
is-increasing-hlevel (S (S n)) A p = λ x y → is-increasing-hlevel (S n) (x ≡ y) (p x y)

-- is-hlevel-equiv : ∀ {i j} {A : Set i} {B : Set j} (f : A ≃ B) (n : ℕ) (c : is-hlevel n A) → is-hlevel n B
-- is-hlevel-equiv f 0 c = ((f $ (π₁ c)) , (λ y → ! (inverse-right-inverse f y) ∘ map (π₁ f) (is-contr-path _ c _ _)))
-- is-hlevel-equiv f 1 c = λ x y → equiv-is-inj (f ⁻¹) x y (c _ _)
-- is-hlevel-equiv f (S (S n)) c = λ x y → is-hlevel-equiv ((map (π₁ (f ⁻¹)) {x = x} {y = y} , {!!}) ⁻¹) (S n) (c (f ⁻¹ $ x) (f ⁻¹ $ y))


-- This is the usual definition of h-levels, but the previous one is more convenient and both are equivalent anyway
-- is-hlevel' : ∀ {i} (n : ℕ) (A : Set i) → Set i
-- is-hlevel' O A = is-contr A
-- is-hlevel' (S n) A = (x y : A) → (is-hlevel' n (x ≡ y))

-- hlevel-equiv : ∀ {i} (n : ℕ) (A : Set i) → (is-hlevel' n A → is-hlevel n A)
-- hlevel-equiv O A p = p
-- hlevel-equiv (S O) A p = λ x y → π₁ (p x y)
-- hlevel-equiv (S (S n)) A p = λ x y → hlevel-equiv (S n) (x ≡ y) (p x y)

-- hlevel-equiv2 : ∀ {i} (n : ℕ) (A : Set i) → (is-hlevel n A → is-hlevel' n A)
-- hlevel-equiv2 0 A p = p
-- hlevel-equiv2 (S O) A p = λ x y → contr-path-contr A (y , (λ x' → p x' y)) x y
-- hlevel-equiv2 (S (S n)) A p = λ x y → hlevel-equiv2 (S n) (x ≡ y) (p x y)

