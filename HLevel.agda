{-# OPTIONS --without-K #-}

open import Types
open import Paths

{- Stuff about h-levels that do not require the notion of equivalence or
   function extensionality -}

module HLevel {i} where

-- Definition of h-levels

is-contr : Set i → Set i
is-contr A = Σ A (λ x → ((y : A) → y ≡ x))

is-hlevel : (n : ℕ) → (Set i → Set i)
is-hlevel O A = is-contr A
is-hlevel (S n) A = (x y : A) → is-hlevel n (x ≡ y)

is-prop = is-hlevel 1
is-set  = is-hlevel 2
is-gpd  = is-hlevel 3

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
    lemma (refl _) = refl _

    canon-path : {x y : A} (p : x ≡ y) → p ≡ c x y
    canon-path (refl y) = anti-whisker-right (c y y) (lemma (c y y))

  -- h-levels are increasing
  hlevel-is-hlevel-S : {A : Set i} (n : ℕ)
    → (is-hlevel n A → is-hlevel (S n) A)
  hlevel-is-hlevel-S O q = all-paths-is-prop (λ x y → π₂ q x ∘ ! (π₂ q y))
  hlevel-is-hlevel-S (S n) q = λ x y → hlevel-is-hlevel-S n (q x y)

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
  
    get-path-eq : {u : A} (r : u ≡ u) → get-path r ≡ get-path (refl _)
    get-path-eq {u} r with dec u u
    get-path-eq r | inl q = refl q
    get-path-eq r | inr r⊥ = abort-nondep (r⊥ (refl _))
  
    lemma : {u v : A} (r : u ≡ v) → r ∘ get-path (refl _) ≡ get-path r
    lemma (refl _) = refl _
  
    paths-A-is-prop : {u v : A} (q : u ≡ v) → is-prop (u ≡ v)
    paths-A-is-prop (refl u) =
      hlevel-is-hlevel-S 0
        (refl u , λ r → anti-whisker-right (get-path (refl _))
                                           (lemma r ∘ get-path-eq r))

module _ {A : Set i} where
  abstract
    contr-has-all-paths : is-contr A → has-all-paths A
    contr-has-all-paths c x y = π₂ c x ∘ ! (π₂ c y)
  
    prop-has-all-paths : is-prop A → has-all-paths A
    prop-has-all-paths c x y = π₁ (c x y)
    
    inhab-prop-is-contr : A → is-prop A → is-contr A
    inhab-prop-is-contr x₀ p = (x₀ , λ y → π₁ (p y x₀))
  
    contr-is-hlevel : (n : ℕ) → (is-contr A → is-hlevel n A)
    contr-is-hlevel 0 p = p
    contr-is-hlevel (S n) p = hlevel-is-hlevel-S n (contr-is-hlevel n p)
  
    prop-is-hlevel-S : (n : ℕ) → (is-prop A → is-hlevel (S n) A)
    prop-is-hlevel-S 0 p = p
    prop-is-hlevel-S (S n) p = hlevel-is-hlevel-S (S n) (prop-is-hlevel-S n p)
  
    set-is-hlevel-SS : (n : ℕ) → (is-set A → is-hlevel (S (S n)) A)
    set-is-hlevel-SS 0 p = p
    set-is-hlevel-SS (S n) p = hlevel-is-hlevel-S (S (S n))
                                                  (set-is-hlevel-SS n p)
  
    contr-is-prop : is-contr A → is-prop A
    contr-is-prop = contr-is-hlevel 1

    contr-is-set : is-contr A → is-set A
    contr-is-set = contr-is-hlevel 2

    contr-is-gpd : is-contr A → is-gpd A
    contr-is-gpd = contr-is-hlevel 3

    prop-is-set : is-prop A → is-set A
    prop-is-set = prop-is-hlevel-S 1

    prop-is-gpd : is-prop A → is-gpd A
    prop-is-gpd = prop-is-hlevel-S 2

    set-is-gpd : is-set A → is-gpd A
    set-is-gpd = set-is-hlevel-SS 1

    -- If [A] is of h-level [n], then so does [x ≡ y] for [x y : A]
    ≡-is-hlevel : (n : ℕ) {x y : A}
      → (is-hlevel n A → is-hlevel n (x ≡ y))
    ≡-is-hlevel O p = (contr-has-all-paths p _ _ , unique-path) where
      unique-path : {u v : A} (q : u ≡ v)
        → q ≡ contr-has-all-paths p u v
      unique-path (refl _) = ! (opposite-right-inverse (π₂ p _))
    ≡-is-hlevel (S n) {x} {y} p = hlevel-is-hlevel-S n (p x y) 

    -- The type of paths to a fixed point is contractible
    pathto-is-contr : (x : A) → is-contr (Σ A (λ t → t ≡ x))
    pathto-is-contr x = ((x , refl x) , pathto-unique-path) where
      pathto-unique-path : {u : A} (pp : Σ A (λ t → t ≡ u)) → pp ≡ (u , refl u)
      pathto-unique-path (.u , refl u) = refl _

abstract
  -- Unit is contractible
  -- I do not need to specify the universe level because in this file [is-contr]
  -- is not yet universe polymorphic ([i] is a global argument)
  unit-is-contr : is-contr unit
  unit-is-contr = (tt , λ y → refl tt)

  unit-is-hlevel : (n : ℕ) → is-hlevel n unit
  unit-is-hlevel n = contr-is-hlevel n unit-is-contr

  -- [unit-is-hlevel#instance] produces unsolved metas
  unit-is-hlevel-S#instance : {n : ℕ} → is-hlevel (S n) unit
  unit-is-hlevel-S#instance = contr-is-hlevel _ unit-is-contr

  unit-is-prop : is-prop unit
  unit-is-prop = unit-is-hlevel 1

  unit-is-set : is-set unit
  unit-is-set = unit-is-hlevel 2

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
  bool-has-dec-eq true true = inl (refl true)
  bool-has-dec-eq true false = inr bool-true≢false
  bool-has-dec-eq false true = inr bool-false≢true
  bool-has-dec-eq false false = inl (refl false)

  bool-is-set : is-set bool
  bool-is-set = dec-eq-is-set bool-has-dec-eq

  ⊥-is-prop : is-prop ⊥
  ⊥-is-prop ()