{-# OPTIONS --without-K #-}

open import Base
open import CategoryTheory.PullbackDef

module CategoryTheory.PullbackIsPullback {i} (A B C : Set i) (f : A → C) (g : B → C) where

import CategoryTheory.PullbackUP as PullbackUP
open PullbackUP A B C f g (λ _ → unit)

pullback-cocone : cocone (pullback A B C f g)
pullback-cocone = (pullback.a A B C f g , pullback.b A B C f g , pullback.h A B C f g)

factor-pullback : (E : Set i) → (cocone E → (E → pullback A B C f g))
factor-pullback E (top→A , top→B , h) x = (top→A x , top→B x , h x)

pullback-is-pullback : is-pullback (pullback A B C f g) pullback-cocone
pullback-is-pullback E = iso-is-eq _ (factor-pullback E) (λ y → refl _) (λ f → refl _)
