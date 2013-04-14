{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.PathGroupoid

module lib.PathFunctor {i} {A : Type i} where

!-ap : ∀ {j} {B : Type j} (f : A → B) {x y : A} (p : x == y)
  → ! (ap f p) == ap f (! p)
!-ap f idp = idp

ap-! : ∀ {j} {B : Type j} (f : A → B) {x y : A} (p : x == y)
  → ap f (! p) == ! (ap f p)
ap-! f idp = idp

∙-ap : ∀ {j} {B : Type j} (f : A → B) {x y z : A} (p : x == y) (q : y == z)
  → ap f p ∙ ap f q == ap f (p ∙ q)
∙-ap f _ idp = idp

ap-∙ : ∀ {j} {B : Type j} (f : A → B) {x y z : A} (p : x == y) (q : y == z)
  → ap f (p ∙ q) == ap f p ∙ ap f q
ap-∙ f _ idp = idp

∘-ap : ∀ {j k} {B : Type j} {C : Type k} (g : B → C) (f : A → B)
  {x y : A} (p : x == y) → ap g (ap f p) == ap (g ∘ f) p
∘-ap f g idp = idp

ap-∘ : ∀ {j k} {B : Type j} {C : Type k} (g : B → C) (f : A → B)
  {x y : A} (p : x == y) → ap (g ∘ f) p == ap g (ap f p)
ap-∘ f g idp = idp

ap-cst : ∀ {j} {B : Type j} (b : B) {x y : A} (p : x == y)
  → ap (cst b) p == idp
ap-cst b idp = idp

ap-id : {u v : A} (p : u == v) → ap (id A) p == p
ap-id idp = idp
