{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.PathGroupoid

module lib.NType {i} where

{- Definition of contractible types and truncation levels -}

is-contr : Type i → Type i
is-contr A = Σ A (λ x → ((y : A) → x == y))

has-level : ℕ₋₂ → (Type i → Type i)
has-level ⟨-2⟩ A = is-contr A
has-level (S n) A = (x y : A) → has-level n (x == y)

is-prop = has-level ⟨-1⟩
is-set  = has-level ⟨0⟩

{- To be a mere proposition, it is sufficient that all points are equal -}

has-all-paths : Type i → Type i
has-all-paths A = (x y : A) → x == y

abstract
  all-paths-is-prop : {A : Type i} → (has-all-paths A → is-prop A)
  all-paths-is-prop {A} c x y = (c x y , canon-path) where

    canon-path : {x y : A} (p : x == y) → c x y == p
    canon-path {.y} {y} idp =
      c y y               =⟨ lemma (! (c y y)) ⟩
      (! (c y y)) ∙ c y y =⟨ !-inv-l (c y y) ⟩
      idp ∎  where

      lemma : {x y : A} (p : x == y) → c x y == p ∙ c y y
      lemma idp = idp

{- Truncation levels are cumulative -}
abstract
  raise-level : {A : Type i} (n : ℕ₋₂)
    → (has-level n A → has-level (S n) A)
  raise-level ⟨-2⟩ q =
    all-paths-is-prop (λ x y → ! (snd q x) ∙ snd q y)
  raise-level (S n) q =
    λ x y → raise-level n (q x y)

{- Having decidable equality is stronger that being a set -}

has-dec-eq : Type i → Type i
has-dec-eq A = (x y : A) → Coprod (x == y) (x ≠ y)

abstract
  dec-eq-is-set : {A : Type i} → (has-dec-eq A → is-set A)
  dec-eq-is-set {A} d x y = all-paths-is-prop UIP where

   UIP : {x y : A} (p q : x == y) -> p == q
   UIP {x} idp q with d x x | lemma q  where

     T : {x y : A} → x == y → Type i
     T {x} {y} p =
       match (d x y) withl (λ b → match (d x x) withl (λ b' → p == ! b' ∙ b)
                                                withr (λ _ → Lift Empty))
                     withr (λ _ → Lift Empty)

     lemma : {x y : A} → (p : x == y) -> T p
     lemma {x} idp with (d x x)
     lemma idp | inl a = ! (!-inv-l a)
     lemma idp | inr r = lift (r idp)

   UIP idp q | inl a | p' = ! (!-inv-l a) ∙ (! p')
   UIP idp q | inr r | _ = Empty-elim (r idp)

{- Relationships between levels -}

module _ {A : Type i} where
  abstract
    contr-has-all-paths : is-contr A → has-all-paths A
    contr-has-all-paths c x y = ! (snd c x) ∙ snd c y

    prop-has-all-paths : is-prop A → has-all-paths A
    prop-has-all-paths c x y = fst (c x y)

    inhab-prop-is-contr : A → is-prop A → is-contr A
    inhab-prop-is-contr x₀ p = (x₀ , λ y → fst (p x₀ y))

    inhab-to-contr-is-prop : (A → is-contr A) → is-prop A
    inhab-to-contr-is-prop c = all-paths-is-prop $
      λ x y → ! (snd (c x) x) ∙ snd (c x) y

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
    =-preserves-level : (n : ℕ₋₂) {x y : A}
      → (has-level n A → has-level n (x == y))
    =-preserves-level ⟨-2⟩ p = (contr-has-all-paths p _ _ , unique-path) where
      unique-path : {u v : A} (q : u == v)
        → contr-has-all-paths p u v == q
      unique-path idp = !-inv-l (snd p _)
    =-preserves-level (S n) {x} {y} p = raise-level n (p x y)

    =-preserves-set : {x y : A} → (is-set A → is-set (x == y))
    =-preserves-set = =-preserves-level ⟨0⟩

    =-preserves-prop : {x y : A} → (is-prop A → is-prop (x == y))
    =-preserves-prop = =-preserves-level ⟨-1⟩

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
