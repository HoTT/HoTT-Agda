{-# OPTIONS --without-K #-}

open import Types
open import Functions
open import Paths
open import Contractible
open import Equivalences
open import Univalence
open import Funext

module HLevel where

-- Every map between contractible types is an equivalence
abstract
  contr-equiv-contr : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) (cA : is-contr A) (cB : is-contr B) → is-equiv f
  contr-equiv-contr {i} {j} {A} {B} f cA cB =
    λ y → ((π₁ cA , (is-contr-path B cB _ _))
          , (λ y' → total-path (is-contr-path A cA _ _)
                               (is-contr-path _ (path-contr-contr B cB _ _) _ _)))

-- Definition of h-levels

is-hlevel : ∀ {i} (n : ℕ) (A : Set i) → Set i
is-hlevel O A = is-contr A
is-hlevel (S n) A = (x y : A) → (is-hlevel n (x ≡ y))

is-prop : ∀ {i} (A : Set i) → Set i
is-prop = is-hlevel 1

is-set : ∀ {i} (A : Set i) → Set i
is-set = is-hlevel 2

is-gpd : ∀ {i} (A : Set i) → Set i
is-gpd = is-hlevel 3

-- Another definition of [is-prop] (both are equivalent)
has-all-paths : ∀ {i} (A : Set i) → Set i
has-all-paths A = (x y : A) → x ≡ y

-- In a prop', every path is equal to the canonical path
all-paths-canon-path : ∀ {i} (A : Set i) (c : has-all-paths A) {x y : A} (p : x ≡ y) → p ≡ c x y
all-paths-canon-path A c (refl _) = ! (lemma2 A c _) where

  lemma1 : ∀ {i} (A : Set i) (c : has-all-paths A) {x y : A} (p : x ≡ y) → p ∘ c y y ≡ c x y
  lemma1 A c (refl _) = refl _

  -- We apply the previous lemma with [p = c y y]
  lemma2 : ∀ {i} (A : Set i) (c : has-all-paths A) (y : A) → c y y ≡ refl y
  lemma2 A c y = anti-whisker-left (c y y) (lemma1 A c (c y y) ∘ ! (refl-right-unit _))

-- If we have [has-all-paths A], then [A] is a proposition
all-paths-is-prop : ∀ {i} {A : Set i} (c : has-all-paths A) → is-prop A
all-paths-is-prop c x y = (c x y , all-paths-canon-path _ c)

is-contr-is-prop : ∀ {i} (A : Set i) → is-prop (is-contr A)
is-contr-is-prop A = all-paths-is-prop
  (λ x y → total-path (π₂ y (π₁ x))
             (funext-dep
               (λ x' → (trans-A→Pxy A (λ x0 y' → y' ≡ x0) (π₂ y (π₁ x)) (π₂ x) x'
                       ∘ trans-a≡x (π₂ y (π₁ x)) (π₂ x x'))
                       ∘ lemma-is-contr-is-prop y (π₂ x x')))) where

  lemma-is-contr-is-prop : (c : is-contr A) {x y : A} (p : x ≡ y) → p ∘ π₂ c y ≡ π₂ c x
  lemma-is-contr-is-prop c (refl _) = refl _

-- h-levels are increasing
is-increasing-hlevel : ∀ {i} (n : ℕ) (A : Set i) → is-hlevel n A → is-hlevel (S n) A
is-increasing-hlevel O A p = all-paths-is-prop (λ x y → π₂ p x ∘ ! (π₂ p y))
is-increasing-hlevel (S n) A p = λ x y → is-increasing-hlevel n (x ≡ y) (p x y)

-- Equivalent types have the same h-level
equiv-types-hlevel : ∀ {i j} {A : Set i} {B : Set j} (n : ℕ) (f : A ≃ B) (c : is-hlevel n A) → is-hlevel n B
equiv-types-hlevel O f c = ((f $ (π₁ c)) , (λ y → ! (inverse-right-inverse f y) ∘ map (π₁ f) (is-contr-path _ c _ _)))
equiv-types-hlevel (S n) f c = λ x y → equiv-types-hlevel n (equiv-map (f ⁻¹) x y ⁻¹) (c (f ⁻¹ $ x) (f ⁻¹ $ y))

pi-is-prop : ∀ {i j} {A : Set i} {P : A → Set j} (p : (x : A) → is-prop (P x)) → is-prop ((x : A) → P x)
pi-is-prop p = all-paths-is-prop (λ f g → funext-dep (λ x → π₁ (p x (f x) (g x))))

pi-hlevel : ∀ {i j} (n : ℕ) {A : Set i} {P : A → Set j} (p : (x : A) → is-hlevel n (P x)) → is-hlevel n ((x : A) → P x)
pi-hlevel O p = ((λ x → π₁ (p x)) , (λ f → funext-dep (λ x → π₂ (p x) (f x))))
pi-hlevel 1 p = pi-is-prop p
pi-hlevel (S n) p = λ f g → equiv-types-hlevel n (funext-dep , funext-dep-is-equiv) (pi-hlevel n (λ x → p x (f x) (g x)))

→-hlevel : ∀ {i j} (n : ℕ) {A : Set i} {B : Set j} (p : is-hlevel n B) → is-hlevel n (A → B)
→-hlevel n p = pi-hlevel n (λ _ → p)

is-hlevel-is-prop : ∀ {i} (n : ℕ) (A : Set i) → is-prop (is-hlevel n A)
is-hlevel-is-prop O A = is-contr-is-prop A
is-hlevel-is-prop (S n) A = pi-is-prop (λ x → pi-is-prop (λ x' → is-hlevel-is-prop n (x ≡ x')))

dec-eq : ∀ {i} (A : Set i) → Set i
dec-eq A = (x y : A) → (x ≡ y) ⊔ (x ≢ y)

-- A type with a decidable equality is a set
dec-eq-is-set : ∀ {i} (A : Set i) (dec : dec-eq A) → is-set A
dec-eq-is-set A dec x y with dec x y
dec-eq-is-set A dec x y | inl q = paths-dec-eq-is-prop q where

  -- The fact that equality is decidable on A gives a canonical path parallel to every path [p], depending only on the ends
  get-path : {u v : A} (p : u ≡ v) → u ≡ v
  get-path {u} {v} p with dec u v
  get-path p | inl q = q
  get-path {u} {v} p | inr p⊥ = abort-nondep (p⊥ p)

  get-path-eq : {u v : A} (p q : u ≡ v) → get-path p ≡ get-path q
  get-path-eq {u} {v} p q with dec u v
  get-path-eq p q | inl _ = refl _
  get-path-eq p q | inr p⊥ = abort-nondep (p⊥ p)

  get-path-get-path : {u v : A} (p : u ≡ v) → get-path (get-path p) ≡ get-path p
  get-path-get-path {u} {v} p with dec u v
  get-path-get-path p | inl q = refl _
  get-path-get-path p | inr p⊥ = abort-nondep (p⊥ p)

  lemma : {u v : A} (p : u ≡ v) → p ∘ get-path (refl _) ≡ get-path p
  lemma (refl _) = refl _

  lemma1 : (a : A) → get-path (refl a) ≡ refl a
  lemma1 a = anti-whisker-left (get-path (refl a)) (lemma (get-path (refl a)) ∘ (get-path-get-path (refl a) ∘ ! (refl-right-unit (get-path (refl a)))))

  lemma2 : {u v : A} (p : u ≡ v) → get-path p ≡ p
  lemma2 p = ! (lemma p) ∘ ((map (λ u → p ∘ u) (lemma1 _)) ∘ (refl-right-unit _))

  paths-dec-eq-is-prop : {u v : A} (p : u ≡ v) → is-prop (u ≡ v)
  paths-dec-eq-is-prop p = all-paths-is-prop (λ q r → ! (lemma2 q) ∘ (get-path-eq q r ∘ lemma2 r))

dec-eq-is-set A dec x y | inr p⊥ = λ p q → abort-nondep (p⊥ p)

unit-is-prop : ∀ {i} → is-prop (unit {i})
unit-is-prop = is-increasing-hlevel O _ unit-is-contr

unit-is-set : ∀ {i} → is-set (unit {i})
unit-is-set = is-increasing-hlevel 1 _ unit-is-prop

sigma-hlevel : ∀ {i j} (n : ℕ) {A : Set i} {P : A → Set j} (p : is-hlevel n A) (q : (x : A) → is-hlevel n (P x)) → is-hlevel n (Σ A P)
sigma-hlevel O p q = ((π₁ p , (π₁ (q (π₁ p)))) , (λ y → total-path (π₂ p _) (π₂ (q _) _)))
sigma-hlevel (S n) p q = λ x y → equiv-types-hlevel n total-path-equiv (sigma-hlevel n (p _ _) (λ _ → q _ _ _))

×-hlevel : ∀ {i j} (n : ℕ) {A : Set i} {B : Set j} (pA : is-hlevel n A) (pB : is-hlevel n B) → is-hlevel n (A × B)
×-hlevel n pA pB = sigma-hlevel n pA (λ x → pB)

subset-is-set : ∀ {i j} (A : Set i) ⦃ p : is-set A ⦄ (P : A → Set j) ⦃ q : (x : A) → is-prop (P x) ⦄ → is-set (Σ A P)
subset-is-set A ⦃ p ⦄ P ⦃ q ⦄ = sigma-hlevel 2 p (λ x → is-increasing-hlevel 1 (P x) (q x))

is-equiv-is-prop : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → is-prop (is-equiv f)
is-equiv-is-prop f = pi-is-prop (λ x → is-contr-is-prop _)

bool-dec-eq : dec-eq bool
bool-dec-eq true true = inl (refl true)
bool-dec-eq true false = inr (λ ())
bool-dec-eq false true = inr (λ ())
bool-dec-eq false false = inl (refl false)

bool-is-set : is-set bool
bool-is-set = dec-eq-is-set bool bool-dec-eq

