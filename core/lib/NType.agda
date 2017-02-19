{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.Relation

module lib.NType where

module _ {i} where

  {- Definition of contractible types and truncation levels -}

  is-contr : Type i → Type i
  is-contr A = Σ A (λ x → ((y : A) → x == y))

  has-level : ℕ₋₂ → (Type i → Type i)
  has-level ⟨-2⟩ A = is-contr A
  has-level (S n) A = (x y : A) → has-level n (x == y)

  is-prop = has-level -1
  is-set  = has-level 0

  {- To be a mere proposition, it is sufficient that all points are equal -}

  has-all-paths : Type i → Type i
  has-all-paths A = (x y : A) → x == y

  -- experimental version for more computational rules
  all-paths-is-prop✭ : {A : Type i} → (has-all-paths A → is-prop A)
  all-paths-is-prop✭ {A} c x y = (c x y , canon-path) where

    canon-path : {x y : A} (p : x == y) → c x y == p
    canon-path {.y} {y} idp =
      c y y               =⟨ lemma (! (c y y)) ⟩
      (! (c y y)) ∙ c y y =⟨ !-inv-l (c y y) ⟩
      idp =∎  where

      lemma : {x y : A} (p : x == y) → c x y == p ∙ c y y
      lemma idp = idp

  abstract
    all-paths-is-prop : {A : Type i} → (has-all-paths A → is-prop A)
    all-paths-is-prop = all-paths-is-prop✭

  {- Truncation levels are cumulative -}
  abstract
    raise-level : {A : Type i} (n : ℕ₋₂)
      → (has-level n A → has-level (S n) A)
    raise-level ⟨-2⟩ q =
      all-paths-is-prop (λ x y → ! (snd q x) ∙ snd q y)
    raise-level (S n) q =
      λ x y → raise-level n (q x y)

  {- Having decidable equality is stronger that being a set -}

  has-dec-onesided-eq : {A : Type i} → A → Type i
  has-dec-onesided-eq x = ∀ y → Dec (x == y)

  has-dec-eq : Type i → Type i
  has-dec-eq A = (x : A) → has-dec-onesided-eq x

  -- experimental version for more computational rules
  dec-onesided-eq-is-prop✭ : {A : Type i} (x : A)
    → has-dec-onesided-eq x → (∀ y → is-prop (x == y))
  dec-onesided-eq-is-prop✭ {A} x d y = all-paths-is-prop✭ UIP where

    T : {y : A} → x == y → Type i
    T {y} p with d x | d y
    T {y} p | inr _  | _      = Lift ⊥
    T {y} p | inl _  | inr _  = Lift ⊥
    T {y} p | inl dx | inl dy = ! dx ∙ dy == p

    lemma : {y : A} → (p : x == y) → T p
    lemma idp with d x
    lemma idp | inl r  = !-inv-l r
    lemma idp | inr r⊥ = lift (r⊥ idp)

    UIP : {y : A} (p q : x == y) → p == q
    UIP idp q with d x | lemma q where
    UIP idp q | inl r  | s = ! (!-inv-l r) ∙' s
    UIP idp q | inr r⊥ | _ = Empty-elim (r⊥ idp)

  -- experimental version for more computational rules
  dec-eq-is-set✭ : {A : Type i} → has-dec-eq A → is-set A
  dec-eq-is-set✭ d x y = dec-onesided-eq-is-prop✭ x (d x) y

  abstract
    dec-onesided-eq-is-prop : {A : Type i} (x : A)
      → has-dec-onesided-eq x → (∀ y → is-prop (x == y))
    dec-onesided-eq-is-prop = dec-onesided-eq-is-prop✭

    dec-eq-is-set : {A : Type i} → has-dec-eq A → is-set A
    dec-eq-is-set = dec-eq-is-set✭

  {- Relationships between levels -}

  module _ {A : Type i} where
    prop-has-all-paths✭ : is-prop A → has-all-paths A
    prop-has-all-paths✭ c x y = fst (c x y)

    abstract
      contr-has-all-paths : is-contr A → has-all-paths A
      contr-has-all-paths c x y = ! (snd c x) ∙ snd c y

      prop-has-all-paths : is-prop A → has-all-paths A
      prop-has-all-paths = prop-has-all-paths✭

      inhab-prop-is-contr : A → is-prop A → is-contr A
      inhab-prop-is-contr x₀ p = (x₀ , λ y → fst (p x₀ y))

      inhab-to-contr-is-prop : (A → is-contr A) → is-prop A
      inhab-to-contr-is-prop c = all-paths-is-prop $
        λ x y → ! (snd (c x) x) ∙ snd (c x) y

      inhab-to-prop-is-prop : (A → is-prop A) → is-prop A
      inhab-to-prop-is-prop c x y = c x x y

      contr-has-level : {n : ℕ₋₂} → (is-contr A → has-level n A)
      contr-has-level {n = ⟨-2⟩} p = p
      contr-has-level {n = S n} p = raise-level n (contr-has-level p)

      prop-has-level-S : {n : ℕ₋₂} → (is-prop A → has-level (S n) A)
      prop-has-level-S {n = ⟨-2⟩} p = p
      prop-has-level-S {n = S n} p = raise-level (S n) (prop-has-level-S p)

      set-has-level-SS : {n : ℕ₋₂} → (is-set A → has-level (S (S n)) A)
      set-has-level-SS {n = ⟨-2⟩} p = p
      set-has-level-SS {n = S n} p = raise-level (S (S n)) (set-has-level-SS p)

      contr-is-prop : is-contr A → is-prop A
      contr-is-prop = contr-has-level

      contr-is-set : is-contr A → is-set A
      contr-is-set = contr-has-level

      prop-is-set : is-prop A → is-set A
      prop-is-set = prop-has-level-S

      {- If [A] has level [n], then so does [x == y] for [x y : A] -}
      =-preserves-level : {n : ℕ₋₂} {x y : A}
        → (has-level n A → has-level n (x == y))
      =-preserves-level {⟨-2⟩} p = (contr-has-all-paths p _ _ , unique-path) where
        unique-path : {u v : A} (q : u == v)
          → contr-has-all-paths p u v == q
        unique-path idp = !-inv-l (snd p _)
      =-preserves-level {S n} {x} {y} p = raise-level n (p x y)

      =-preserves-set : {x y : A} → (is-set A → is-set (x == y))
      =-preserves-set = =-preserves-level

      =-preserves-prop : {x y : A} → (is-prop A → is-prop (x == y))
      =-preserves-prop = =-preserves-level

    {- The type of paths from a fixed point is contractible -}
    pathfrom-is-contr : (x : A) → is-contr (Σ A (λ t → x == t))
    pathfrom-is-contr x = ((x , idp) , pathfrom-unique-path) where
      pathfrom-unique-path : {u : A} (pp : Σ A (λ t → u == t)) → (u , idp) == pp
      pathfrom-unique-path (u , idp) = idp

    {- The type of paths to a fixed point is contractible -}
    pathto-is-contr : (x : A) → is-contr (Σ A (λ t → t == x))
    pathto-is-contr x = ((x , idp) , pathto-unique-path) where
      pathto-unique-path : {u : A} (pp : Σ A (λ t → t == u)) → (u , idp) == pp
      pathto-unique-path (u , idp) = idp

    {-
    If [B] is a fibration over a contractible type [A], then any point in any
    fiber of [B] gives a section
    -}
    contr-has-section : ∀ {j} {A : Type i} {B : A → Type j}
      → (is-contr A → (x : A) → (u : B x) → Π A B)
    contr-has-section {B = B} (x , p) x₀ y₀ t = transport B (! (p x₀) ∙ p t) y₀

{- Subtypes -}

module _ {i} (A : Type i) where
  SubtypeProp : ∀ j → Type (lmax i (lsucc j))
  SubtypeProp j = Σ (A → Type j) (λ P → ∀ a → is-prop (P a))

module SubtypeProp {i j} {A : Type i} (P : SubtypeProp A j) where
  prop = fst P
  level = snd P

module _ {i j} {A : Type i} (P : SubtypeProp A j) where
  private
    module P = SubtypeProp P

  Subtype : Type (lmax i j)
  Subtype = Σ A P.prop
