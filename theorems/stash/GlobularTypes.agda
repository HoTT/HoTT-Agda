{-# OPTIONS --without-K --rewriting --copatterns #-}

open import HoTT

module experimental.GlobularTypes where

{- Globular types as a coinductive record -}
record Glob (i : ULevel) : Type (lsucc i) where
  coinductive
  constructor glob
  field
    Ob : Type i
    Hom : (a b : Ob) → Glob i
open Glob public

{- The terminal globular type -}
Unit-glob : Glob lzero
Ob Unit-glob = Unit
Hom Unit-glob _ _ = Unit-glob

{- The tower of identity types -}
Id-glob : ∀ {i} (A : Type i) → Glob i
Ob (Id-glob A) = A
Hom (Id-glob A) a b = Id-glob (a == b)

{- Bisimulation between globular types -}
record _~_ {i} (G H : Glob i) : Type (lsucc i) where
  coinductive
  constructor glob~
  field
    Ob= : Ob G == Ob H
    Hom= : {a : Ob G} {a' : Ob H} (p : a == a' [ (λ x → x) ↓ Ob= ])
           {b : Ob G} {b' : Ob H} (q : b == b' [ (λ x → x) ↓ Ob= ])
           → Hom G a b ~ Hom H a' b'
open _~_ public

=-to-~ : ∀ {i} {G H : Glob i} → G == H → G ~ H
Ob= (=-to-~ p) = ap Ob p
Hom= (=-to-~ p) q r =
  =-to-~ (↓-app→cst-out (↓-→-out (apd Hom p)
                                 (↓-ap-out _ Ob p q))
                        (↓-ap-out _ Ob p r))
-- The definition of [Hom= (=-to-~ p) q r] would/should just be
-- [=-to-~ (apd Hom p q r)] in infinite-dimensional type theory, but here we
-- need to add a lot of non-sense to make it type-check.

{-
We postulate that bisimilarity is equality, because this should be true.
-}
postulate
  bisim-is-equiv : ∀ {i} {G H : Glob i} → is-equiv (=-to-~ :> (G == H → G ~ H))

bisim-equiv : ∀ {i} {G H : Glob i} → (G == H) ≃ (G ~ H)
bisim-equiv = (=-to-~ , bisim-is-equiv)

bisim : ∀ {i} {G H : Glob i} → (G ~ H) → G == H
bisim e = <– bisim-equiv e

{-
The type of globular types is the terminal coalgebra of the appropriate thing.
This is proved in the following two lemmas.
-}

Glob-corec : ∀ {i} {A : Type (lsucc i)} (Ob* : A → Type i)
  (Hom* : (x : A) (a b : Ob* x) → A) → (A → Glob i)
Ob (Glob-corec Ob* Hom* x) = Ob* x
Hom (Glob-corec Ob* Hom* x) a b = Glob-corec Ob* Hom* (Hom* x a b)

eta : ∀ {i} {A : Type (lsucc i)} (Ob* : A → Type i)
  (Hom* : (x : A) (a b : Ob* x) → A)
  (f g : A → Glob i) (s : (x : A) → f x ~ g x) → f == g
eta Ob* Hom* f g s = λ= λ x → bisim (s x)
