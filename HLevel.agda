{-# OPTIONS --without-K #-}

open import Types
open import Paths

{- Stuff about truncation levels (aka h-levers) that do not require the notion
   of equivalence or function extensionality -}

module HLevel {i} where

-- Definition of truncation levels

is-contr : Set i → Set i
is-contr A = Σ A (λ x → ((y : A) → y ≡ x))

is-truncated : ℕ₋₂ → (Set i → Set i)
is-truncated ⟨-2⟩ A = is-contr A
is-truncated (S n) A = (x y : A) → is-truncated n (x ≡ y)

is-prop = is-truncated ⟨-1⟩
is-set  = is-truncated ⟨0⟩
is-gpd  = is-truncated ⟨1⟩

-- The original notion of h-level can be defined in the following way.
-- We won’t use this definition though.
is-hlevel : ℕ → (Set i → Set i)
is-hlevel n = is-truncated (n -2)

-- The following property is equivalent to being a proposition
has-all-paths : Set i → Set i
has-all-paths A = (x y : A) → x ≡ y

-- Having decidable equality is stronger that being a set
has-dec-eq : Set i → Set i
has-dec-eq A = (x y : A) → (x ≡ y) ⊔ (x ≢ y)

abstract
  all-paths-is-prop : {A : Set i} → (has-all-paths A → is-prop A)
  all-paths-is-prop {A} c x y = (c x y , canon-path) where
    lemma : {x y : A} (p : x ≡ y) → c x y ≡ p ∘ c y y
    lemma refl = refl

    canon-path : {x y : A} (p : x ≡ y) → p ≡ c x y
    canon-path {.y} {y} refl = anti-whisker-right (c y y) (lemma (c y y))

  -- Truncation levels are cumulative
  truncated-is-truncated-S : {A : Set i} (n : ℕ₋₂)
    → (is-truncated n A → is-truncated (S n) A)
  truncated-is-truncated-S ⟨-2⟩ q =
    all-paths-is-prop (λ x y → π₂ q x ∘ ! (π₂ q y))
  truncated-is-truncated-S (S n) q =
    λ x y → truncated-is-truncated-S n (q x y)

  -- A type with a decidable equality is a set
  dec-eq-is-set : {A : Set i} → (has-dec-eq A → is-set A)
  dec-eq-is-set dec x y with dec x y
  dec-eq-is-set dec x y | inr p⊥ = λ p → abort-nondep (p⊥ p)
  dec-eq-is-set {A} dec x y | inl q = paths-A-is-prop q where

    -- The fact that equality is decidable on A gives a canonical path parallel
    -- to every path [p], depending only on the endpoints
    get-path : {u v : A} (r : u ≡ v) → u ≡ v
    get-path {u} {v} r with dec u v
    get-path r | inl q = q
    get-path r | inr r⊥ = abort-nondep (r⊥ r)

    get-path-eq : {u : A} (r : u ≡ u) → get-path r ≡ get-path refl
    get-path-eq {u} r with dec u u
    get-path-eq r | inl q = refl
    get-path-eq r | inr r⊥ = abort-nondep (r⊥ refl)

    lemma : {u v : A} (r : u ≡ v) → r ∘ get-path refl ≡ get-path r
    lemma refl = refl

    paths-A-is-prop : {u v : A} (q : u ≡ v) → is-prop (u ≡ v)
    paths-A-is-prop {u} {.u} refl =
      truncated-is-truncated-S ⟨-2⟩
        (refl , λ r → anti-whisker-right (get-path refl)
                                         (lemma r ∘ get-path-eq r))

module _ {A : Set i} where
  abstract
    contr-has-all-paths : is-contr A → has-all-paths A
    contr-has-all-paths c x y = π₂ c x ∘ ! (π₂ c y)

    prop-has-all-paths : is-prop A → has-all-paths A
    prop-has-all-paths c x y = π₁ (c x y)

    inhab-prop-is-contr : A → is-prop A → is-contr A
    inhab-prop-is-contr x₀ p = (x₀ , λ y → π₁ (p y x₀))

    contr-is-truncated : (n : ℕ₋₂) → (is-contr A → is-truncated n A)
    contr-is-truncated ⟨-2⟩ p = p
    contr-is-truncated (S n) p =
      truncated-is-truncated-S n (contr-is-truncated n p)

    prop-is-truncated-S : (n : ℕ₋₂) → (is-prop A → is-truncated (S n) A)
    prop-is-truncated-S ⟨-2⟩ p = p
    prop-is-truncated-S (S n) p =
      truncated-is-truncated-S (S n) (prop-is-truncated-S n p)

    set-is-truncated-SS : (n : ℕ₋₂) → (is-set A → is-truncated (S (S n)) A)
    set-is-truncated-SS ⟨-2⟩ p = p
    set-is-truncated-SS (S n) p = truncated-is-truncated-S (S (S n))
                                                  (set-is-truncated-SS n p)

    contr-is-prop : is-contr A → is-prop A
    contr-is-prop = contr-is-truncated ⟨-1⟩

    contr-is-set : is-contr A → is-set A
    contr-is-set = contr-is-truncated ⟨0⟩

    contr-is-gpd : is-contr A → is-gpd A
    contr-is-gpd = contr-is-truncated ⟨1⟩

    prop-is-set : is-prop A → is-set A
    prop-is-set = prop-is-truncated-S ⟨-1⟩

    prop-is-gpd : is-prop A → is-gpd A
    prop-is-gpd = prop-is-truncated-S ⟨0⟩

    set-is-gpd : is-set A → is-gpd A
    set-is-gpd = set-is-truncated-SS ⟨-1⟩

    -- If [A] is n-truncated, then so does [x ≡ y] for [x y : A]
    ≡-is-truncated : (n : ℕ₋₂) {x y : A}
      → (is-truncated n A → is-truncated n (x ≡ y))
    ≡-is-truncated ⟨-2⟩ p = (contr-has-all-paths p _ _ , unique-path) where
      unique-path : {u v : A} (q : u ≡ v)
        → q ≡ contr-has-all-paths p u v
      unique-path refl = ! (opposite-right-inverse (π₂ p _))
    ≡-is-truncated (S n) {x} {y} p = truncated-is-truncated-S n (p x y)

  -- The type of paths to a fixed point is contractible
  pathto-is-contr : (x : A) → is-contr (Σ A (λ t → t ≡ x))
  pathto-is-contr x = ((x , refl) , pathto-unique-path) where
    pathto-unique-path : {u : A} (pp : Σ A (λ t → t ≡ u)) → pp ≡ (u , refl)
    pathto-unique-path (u , refl) = refl

  -- Specilization
  module _ where
    ≡-is-set : {x y : A} → (is-set A → is-set (x ≡ y))
    ≡-is-set = ≡-is-truncated ⟨0⟩

    ≡-is-prop : {x y : A} → (is-prop A → is-prop (x ≡ y))
    ≡-is-prop = ≡-is-truncated ⟨-1⟩

abstract
  -- Unit is contractible
  -- I do not need to specify the universe level because in this file [is-contr]
  -- is not yet universe polymorphic ([i] is a global argument)
  unit-is-contr : is-contr unit
  unit-is-contr = (tt , λ y → refl)

  unit-is-truncated : (n : ℕ₋₂) → is-truncated n unit
  unit-is-truncated n = contr-is-truncated n unit-is-contr

  -- [unit-is-truncated#instance] produces unsolved metas
  unit-is-truncated-S#instance : {n : ℕ₋₂} → is-truncated (S n) unit
  unit-is-truncated-S#instance = contr-is-truncated _ unit-is-contr

  unit-is-prop : is-prop unit
  unit-is-prop = unit-is-truncated ⟨-1⟩

  unit-is-set : is-set unit
  unit-is-set = unit-is-truncated ⟨0⟩

  contr-has-section : ∀ {j} {A : Set i} {P : A → Set j}
    → (is-contr A → (x : A) → (u : P x) → Π A P)
  contr-has-section (x , p) x₀ y₀ t = transport _ (p x₀ ∘ ! (p t)) y₀

private
  bool-true≢false-type : bool {i} → Set
  bool-true≢false-type true  = ⊤
  bool-true≢false-type false = ⊥

abstract
  bool-true≢false : true {i} ≢ false
  bool-true≢false p = transport bool-true≢false-type p tt

  bool-false≢true : false {i} ≢ true
  bool-false≢true p = transport bool-true≢false-type (! p) tt

  bool-has-dec-eq : has-dec-eq bool
  bool-has-dec-eq true true = inl refl
  bool-has-dec-eq true false = inr bool-true≢false
  bool-has-dec-eq false true = inr bool-false≢true
  bool-has-dec-eq false false = inl refl

  bool-is-set : is-set bool
  bool-is-set = dec-eq-is-set bool-has-dec-eq

  ⊥-is-prop : is-prop ⊥
  ⊥-is-prop ()
