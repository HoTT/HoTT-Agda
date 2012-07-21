{-# OPTIONS --without-K #-}

open import Base

module FreeGroup.F2NotCommutative where

import FreeGroup.FreeGroup
open FreeGroup.FreeGroup bool bool-is-set renaming (freegroup to F2)

X : Set
X = bool × bool

X-is-set : is-set X
X-is-set = ×-hlevel 2 bool-is-set bool-is-set

-- [map1] and [map2] are two involutive noncommuting bijections of [X]

map1 : X → X
map1 (true , true) = (true , false)
map1 (true , false) = (true , true)
map1 (false , true) = (false , true)
map1 (false , false) = (false , false)

map2 : X → X
map2 (true , true) = (false , true)
map2 (true , false) = (true , false)
map2 (false , true) = (true , true)
map2 (false , false) = (false , false)

act : bool → (X → X)
act true = map1
act false = map2

act-involutive : (b : bool) (x : X) → (act b (act b x) ≡ x)
act-involutive true (true , true) = refl _
act-involutive true (true , false) = refl _
act-involutive true (false , true) = refl _
act-involutive true (false , false) = refl _
act-involutive false (true , true) = refl _
act-involutive false (true , false) = refl _
act-involutive false (false , true) = refl _
act-involutive false (false , false) = refl _

F2-act-on-X : F2 → (X → X)
F2-act-on-X = freegroup-rec-nondep _
  (idmap _)
  (λ b f → f ◯ act b)
  (λ b f → f ◯ act b)
  (λ b f → funext-dep (λ x → map f (act-involutive b x)))
  (λ b f → funext-dep (λ x → map f (act-involutive b x)))
  (→-hlevel 2 X-is-set)

ab : F2
ab = true · (false · e)

ba : F2
ba = false · (true · e)

true≢false : true ≢ false
true≢false ()

F2-non-commutative : ab ≢ ba
F2-non-commutative p = true≢false (base-path (happly (map F2-act-on-X p) (true , true)))
