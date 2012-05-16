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
contr-contr-equiv {i} {j} {A} {B} f cA cB =
  λ y → ((π₁ cA , (is-contr-path B cB _ _))
        , (λ y' → total-path (is-contr-path A cA _ _)
                             (is-contr-path _ (path-contr-contr B cB _ _) _ _)))

-- Definition of h-levels

is-hlevel : ∀ {i} (n : ℕ) (A : Set i) → Set i
is-hlevel O A = is-contr A
is-hlevel (S n) A = (x y : A) → (is-hlevel n (x ≡ y))

is-prop : ∀ {i} (A : Set i) → Set _
is-prop = is-hlevel 1

is-set : ∀ {i} (A : Set i) → Set _
is-set = is-hlevel 2

is-gpd : ∀ {i} (A : Set i) → Set _
is-gpd = is-hlevel 3

-- Another definition of propositions (both are equivalent)
is-prop' : ∀ {i} (A : Set i) → Set i
is-prop' A = (x y : A) → x ≡ y

-- In a prop', every path is equal to the canonical path
is-prop'-canon-path : ∀ {i} (A : Set i) (c : is-prop' A) {x y : A} (p : x ≡ y) → p ≡ c x y
is-prop'-canon-path A c (refl _) = ! (lemma2 A c _) where

  lemma1 : ∀ {i} (A : Set i) (c : is-prop' A) {x y : A} (p : x ≡ y) → p ∘ c y y ≡ c x y
  lemma1 A c (refl _) = refl _

  -- We apply the previous lemma with [p = c y y]
  lemma2 : ∀ {i} (A : Set i) (c : is-prop' A) (y : A) → c y y ≡ refl y
  lemma2 A c y = anti-whisker-left (c y y) (lemma1 A c (c y y) ∘ ! (refl-right-unit _))

-- The usual definition of [is-prop] is equivalent
is-prop-prop' : ∀ {i} {A : Set i} (c : is-prop' A) → is-prop A
is-prop-prop' c x y = (c x y , is-prop'-canon-path _ c)

is-prop-is-contr : ∀ {i} (A : Set i) → is-prop (is-contr A)
is-prop-is-contr A = is-prop-prop' 
  (λ x y → total-path (π₂ y (π₁ x))
             (funext-dep
               (λ x' → (trans-A→Pxy A (λ x0 y' → y' ≡ x0) (π₂ y (π₁ x)) (π₂ x) x'
                       ∘ trans-a≡x (π₂ y (π₁ x)) (π₂ x x'))
                       ∘ lemma-is-prop-is-contr y (π₂ x x')))) where

  lemma-is-prop-is-contr : (c : is-contr A) {x y : A} (p : x ≡ y) → p ∘ π₂ c y ≡ π₂ c x
  lemma-is-prop-is-contr c (refl _) = refl _

is-prop-pi : ∀ {i j} (A : Set i) (P : A → Set j) (p : (x : A) → is-prop (P x)) → is-prop ((x : A) → P x)
is-prop-pi A P p = is-prop-prop' (λ f g → funext-dep (λ x → π₁ (p x (f x) (g x))))

-- is-prop-is-prop : ∀ {i} (A : Set i) → is-prop (is-prop A)
-- is-prop-is-prop A c c' = funext-dep _ _ (λ x → funext-dep _ _ (λ x' → is-prop'-canon-path _ c' (c x x')))

is-prop-hlevel : ∀ {i} (n : ℕ) (A : Set i) → is-prop (is-hlevel n A)
is-prop-hlevel O A = is-prop-is-contr A
is-prop-hlevel (S n) A = is-prop-pi _ _ (λ x → is-prop-pi _ _ (λ x' → is-prop-hlevel n (x ≡ x')))

-- h-levels are increasing
is-increasing-hlevel : ∀ {i} (n : ℕ) (A : Set i) → is-hlevel n A → is-hlevel (S n) A
is-increasing-hlevel O A p = is-prop-prop' (λ x y → π₂ p x ∘ ! (π₂ p y))
is-increasing-hlevel (S n) A p = λ x y → is-increasing-hlevel n (x ≡ y) (p x y)

-- Equivalent types have the same h-level
is-hlevel-equiv : ∀ {i j} {A : Set i} {B : Set j} (f : A ≃ B) (n : ℕ) (c : is-hlevel n A) → is-hlevel n B
is-hlevel-equiv f O c = ((f $ (π₁ c)) , (λ y → ! (inverse-right-inverse f y) ∘ map (π₁ f) (is-contr-path _ c _ _)))
is-hlevel-equiv f (S n) c = λ x y → is-hlevel-equiv (equiv-map (f ⁻¹) x y ⁻¹) n (c (f ⁻¹ $ x) (f ⁻¹ $ y))

dec-eq : ∀ {i} (A : Set i) → Set i
dec-eq A = (x y : A) → (x ≡ y) ⊔ (x ≡ y → ⊥)

-- A type with a decidable equality is a set
dec-eq-is-set : ∀ {i} (A : Set i) (dec : dec-eq A) → is-set A
dec-eq-is-set A dec x y with dec x y
dec-eq-is-set A dec x y | inl q = dec-is-set-equal q where

  -- The fact that equality is decidable on A gives a canonical path parallel to every path [p], depending only on the ends
  get-path : {u v : A} (p : u ≡ v) → u ≡ v
  get-path {u} {v} p with dec u v
  get-path p | inl q = q
  get-path p | inr p⊥ = abort _ (p⊥ p)

  get-path-eq : {u v : A} (p q : u ≡ v) → get-path p ≡ get-path q
  get-path-eq {u} {v} p q with dec u v
  get-path-eq p q | inl _ = refl _
  get-path-eq p q | inr p⊥ = abort _ (p⊥ p)

  get-path-get-path : {u v : A} (p : u ≡ v) → get-path (get-path p) ≡ get-path p
  get-path-get-path {u} {v} p with dec u v
  get-path-get-path p | inl q = refl _
  get-path-get-path p | inr p⊥ = abort _ (p⊥ p)

  lemma : {u v : A} (p : u ≡ v) → p ∘ get-path (refl _) ≡ get-path p
  lemma (refl _) = refl _

  lemma1 : (a : A) → get-path (refl a) ≡ refl a
  lemma1 a = anti-whisker-left (get-path (refl a)) (lemma (get-path (refl a)) ∘ (get-path-get-path (refl a) ∘ ! (refl-right-unit (get-path (refl a)))))

  lemma2 : {u v : A} (p : u ≡ v) → get-path p ≡ p
  lemma2 p = ! (lemma p) ∘ ((map (λ u → p ∘ u) (lemma1 _)) ∘ (refl-right-unit _))

  dec-is-set-equal : {u v : A} (p : u ≡ v) → is-prop (u ≡ v)
  dec-is-set-equal p = is-prop-prop' (λ q r → ! (lemma2 q) ∘ (get-path-eq q r ∘ lemma2 r))

dec-eq-is-set A dec x y | inr p⊥ = λ p q → abort _ (p⊥ p)