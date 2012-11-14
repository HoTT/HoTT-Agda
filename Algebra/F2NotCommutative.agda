{-# OPTIONS --without-K #-}

open import Base

module Algebra.F2NotCommutative where

import Algebra.FreeGroup
open Algebra.FreeGroup (bool {zero}) renaming (freegroup to F2)

X : Set
X = bool × bool

X-is-set : is-set X
X-is-set = ×-is-truncated _ bool-is-set bool-is-set

pattern a = (true  , true )
pattern b = (true  , false)
pattern c = (false , true )
pattern d = (false , false)

-- [map1] and [map2] are two involutive noncommutating bijections of [X]

map1 : X → X
map1 a = b
map1 b = a
map1 c = c
map1 d = d

map2 : X → X
map2 a = c
map2 b = b
map2 c = a
map2 d = d

act : bool {zero} → (X → X)
act true  = map1
act false = map2

act-involutive : (b : bool) (x : X) → (act b (act b x) ≡ x)
act-involutive true  a = refl _
act-involutive true  b = refl _
act-involutive true  c = refl _
act-involutive true  d = refl _
act-involutive false a = refl _
act-involutive false b = refl _
act-involutive false c = refl _
act-involutive false d = refl _

F2-act-on-X : F2 → (X → X)
F2-act-on-X = freegroup-rec-nondep (X → X)
  (id X)
  (λ b f → f ◯ act b)
  (λ b f → f ◯ act b)
  (λ b f → funext (λ x → map f (act-involutive b x)))
  (λ b f → funext (λ x → map f (act-involutive b x)))
  (→-is-truncated _ X-is-set)

ab : F2
ab = true  · (false · e)

ba : F2
ba = false · (true  · e)

F2-non-commutative : ab ≢ ba
F2-non-commutative p =
  bool-true≢false (base-path (happly (map F2-act-on-X p) a))
