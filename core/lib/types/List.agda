{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Bool
open import lib.types.Int

module lib.types.List where

infixr 60 _::_

data List {i} (A : Type i) : Type i where
  nil : List A
  _::_ : A → List A → List A

module _ {i} {A : Type i} where
  infixr 80 _++_
  _++_ : List A → List A → List A
  nil ++ l = l
  (x :: l₁) ++ l₂ = x :: (l₁ ++ l₂)

  snoc : List A → A → List A
  snoc l a = l ++ (a :: nil)

  ++-unit-r : ∀ l → l ++ nil == l
  ++-unit-r nil      = idp
  ++-unit-r (a :: l) = ap (a ::_) $ ++-unit-r l

  ++-assoc : ∀ l₁ l₂ l₃ → (l₁ ++ l₂) ++ l₃ == l₁ ++ (l₂ ++ l₃)
  ++-assoc nil l₂ l₃ = idp
  ++-assoc (x :: l₁) l₂ l₃ = ap (x ::_) (++-assoc l₁ l₂ l₃)

  -- properties
  module _ {j} (P : A → Type j) where
    data Any : List A → Type (lmax i j) where
      here : ∀ {a} {l} → P a → Any (a :: l)
      there : ∀ {a} {l} → Any l → Any (a :: l)

    data All : List A → Type (lmax i j) where
      nil : All nil
      _::_ : ∀ {a} {l} → P a → All l → All (a :: l)

    Any-dec : (∀ a → Dec (P a)) → (∀ l → Dec (Any l))
    Any-dec _   nil       = inr λ{()}
    Any-dec dec (a :: l) with dec a
    ... | inl p = inl $ here p
    ... | inr ¬p with Any-dec dec l
    ...   | inl ∃p = inl $ there ∃p
    ...   | inr ¬∃p = inr λ{(here p) → ¬p p; (there ∃p) → ¬∃p ∃p}

    Any-++-l : ∀ l₁ l₂ → Any l₁ → Any (l₁ ++ l₂)
    Any-++-l _ _ (here p)   = here p
    Any-++-l _ _ (there ∃p) = there (Any-++-l _ _ ∃p)

    Any-++-r : ∀ l₁ l₂ → Any l₂ → Any (l₁ ++ l₂)
    Any-++-r nil      _ ∃p = ∃p
    Any-++-r (a :: l) _ ∃p = there (Any-++-r l _ ∃p)

    Any-++ : ∀ l₁ l₂ → Any (l₁ ++ l₂) → Any l₁ ⊔ Any l₂
    Any-++ nil       l₂ ∃p         = inr ∃p
    Any-++ (a :: l₁) l₂ (here p)   = inl (here p)
    Any-++ (a :: l₁) l₂ (there ∃p) with Any-++ l₁ l₂ ∃p
    ... | inl ∃p₁ = inl (there ∃p₁)
    ... | inr ∃p₂ = inr ∃p₂

  infix 80 _∈_
  _∈_ : A → List A → Type i
  a ∈ l = Any (_== a) l

  ∈-dec : has-dec-eq A → ∀ a l → Dec (a ∈ l)
  ∈-dec dec a l = Any-dec (_== a) (λ a' → dec a' a) l

  ∈-++-l : ∀ a l₁ l₂ → a ∈ l₁ → a ∈ (l₁ ++ l₂)
  ∈-++-l a = Any-++-l (_== a)

  ∈-++-r : ∀ a l₁ l₂ → a ∈ l₂ → a ∈ (l₁ ++ l₂)
  ∈-++-r a = Any-++-r (_== a)

  ∈-++ : ∀ a l₁ l₂ → a ∈ (l₁ ++ l₂) → (a ∈ l₁) ⊔ (a ∈ l₂)
  ∈-++ a = Any-++ (_== a)

  -- [foldr] in Haskell
  foldr : ∀ {j} {B : Type j} → (A → B → B) → B → List A → B
  foldr f b nil = b
  foldr f b (a :: l) = f a (foldr f b l)

  -- [length] in Haskell
  length : List A → ℕ
  length = foldr (λ _ n → S n) 0

  -- [filter] in Haskell
  -- Note that [Bool] is currently defined as a coproduct.
  filter : ∀ {j k} {Keep : A → Type j} {Drop : A → Type k}
    → ((a : A) → Keep a ⊔ Drop a) → List A → List A
  filter p nil = nil
  filter p (a :: l) with p a
  ... | inl _ = a :: filter p l
  ... | inr _ = filter p l

  -- [reverse] in Haskell
  reverse : List A → List A
  reverse nil = nil
  reverse (x :: l) = snoc (reverse l) x

  reverse-snoc : ∀ a l → reverse (snoc l a) == a :: reverse l
  reverse-snoc a nil = idp
  reverse-snoc a (b :: l) = ap (λ l → snoc l b) (reverse-snoc a l)

  reverse-reverse : ∀ l → reverse (reverse l) == l
  reverse-reverse nil = idp
  reverse-reverse (a :: l) = reverse-snoc a (reverse l) ∙ ap  (a ::_) (reverse-reverse l)

  -- Reasoning about identifications
  List= : ∀ (l₁ l₂ : List A) → Type i
  List= nil       nil       = Lift ⊤
  List= nil       (y :: l₂) = Lift ⊥
  List= (x :: l₁) nil       = Lift ⊥
  List= (x :: l₁) (y :: l₂) = (x == y) × (l₁ == l₂)

  List=-in : ∀ {l₁ l₂ : List A} → l₁ == l₂ → List= l₁ l₂
  List=-in {l₁ = nil} idp = lift unit
  List=-in {l₁ = x :: l} idp = idp , idp

  List=-out : ∀ {l₁ l₂ : List A} → List= l₁ l₂ → l₁ == l₂
  List=-out {l₁ = nil} {l₂ = nil} _ = idp
  List=-out {l₁ = nil} {l₂ = y :: l₂} (lift ())
  List=-out {l₁ = x :: l₁} {l₂ = nil} (lift ())
  List=-out {l₁ = x :: l₁} {l₂ = y :: l₂} (x=y , l₁=l₂) = ap2 _::_ x=y l₁=l₂

module _ {i j} {A : Type i} {B : Type j} (f : A → B) where

  -- [map] in Haskell
  map : List A → List B
  map nil = nil
  map (a :: l) = f a :: map l

  map-++ : ∀ l₁ l₂ → map (l₁ ++ l₂) == map l₁ ++ map l₂
  map-++ nil l₂ = idp
  map-++ (x :: l₁) l₂ = ap (f x ::_) (map-++ l₁ l₂)
{-
  reverse-map : ∀ l → reverse (map l) == map (reverse l)
  reverse-map nil = idp
  reverse-map (x :: l) = {! ! (map-++ (reverse l) (x :: nil)) !}
-}
-- These functions use different [A], [B] or [f].
module _ {i} {A : Type i} where
  -- [concat] in Haskell
  concat : List (List A) → List A
  concat l = foldr _++_ nil l
