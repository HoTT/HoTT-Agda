{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.PathGroupoid

module lib.PathFunctor {i} {A : Type i} where

module _ {j} {B : Type j} (f : A → B) where

  !-ap : {x y : A} (p : x == y)
    → ! (ap f p) == ap f (! p)
  !-ap idp = idp

  ap-! : {x y : A} (p : x == y)
    → ap f (! p) == ! (ap f p)
  ap-! idp = idp

  ∙-ap : {x y z : A} (p : x == y) (q : y == z)
    → ap f p ∙ ap f q == ap f (p ∙ q)
  ∙-ap idp idp = idp

  ap-∙ : {x y z : A} (p : x == y) (q : y == z)
    → ap f (p ∙ q) == ap f p ∙ ap f q
  ap-∙ idp idp = idp

  ∙'-ap : {x y z : A} (p : x == y) (q : y == z)
    → ap f p ∙' ap f q == ap f (p ∙' q)
  ∙'-ap idp idp = idp

  ap-∙' : {x y z : A} (p : x == y) (q : y == z)
    → ap f (p ∙' q) == ap f p ∙' ap f q
  ap-∙' idp idp = idp

module _ {j} {B : A → Type j} (f : Π A B) where

  apd-∙ : {x y z : A} (p : x == y) (q : y == z)
    → apd f (p ∙ q) == apd f p ∙dep apd f q
  apd-∙ idp idp = idp

  apd-∙' : {x y z : A} (p : x == y) (q : y == z)
    → apd f (p ∙' q) == apd f p ∙'dep apd f q
  apd-∙' idp idp = idp

∘-ap : ∀ {j k} {B : Type j} {C : Type k} (g : B → C) (f : A → B)
  {x y : A} (p : x == y) → ap g (ap f p) == ap (g ∘ f) p
∘-ap f g idp = idp

ap-∘ : ∀ {j k} {B : Type j} {C : Type k} (g : B → C) (f : A → B)
  {x y : A} (p : x == y) → ap (g ∘ f) p == ap g (ap f p)
ap-∘ f g idp = idp

ap-cst : ∀ {j} {B : Type j} (b : B) {x y : A} (p : x == y)
  → ap (cst b) p == idp
ap-cst b idp = idp

ap-idf : {u v : A} (p : u == v) → ap (idf A) p == p
ap-idf idp = idp
