{-# OPTIONS --without-K #-}

open import Base

open import Homotopy.PushoutDef

module Homotopy.PushoutIsPushout {i} (D : pushout-diag i) where

import Homotopy.PushoutUP as PushoutUP
open PushoutUP D (λ _ → unit) -- A B C f g (λ _ → unit)

pushout-cone : cone (pushout D)
pushout-cone = (left D , right D , glue D)

factor-pushout : (E : Set i) → (cone E → (pushout D → E))
factor-pushout E (A→top , B→top , h) = pushout-rec-nondep D E A→top B→top h

abstract
  pushout-is-pushout : is-pushout (pushout D) pushout-cone
  pushout-is-pushout E ⦃ tt ⦄ = iso-is-eq _ (factor-pushout E)
    (λ y → map (λ u → _ , _ , u)
               (funext-dep (λ x → pushout-β-glue-nondep D E (cone.A→top y)
                                    (cone.B→top y) (cone.h y) x)))
    (λ f → funext-dep (pushout-rec D _ (λ a → refl _) (λ b → refl _)
      (λ c → trans-fx≡gx
             (pushout-rec-nondep D E (f ◯ left D) (f ◯ right D)
              (λ c' → map f (glue D c')))
             f (glue D c) (refl _)
             ∘ (map (λ u → ! u ∘ map f (glue D c))
                  (pushout-β-glue-nondep D E (f ◯ left D) (f ◯ right D)
                   (λ c' → map f (glue D c')) c)
                  ∘ opposite-left-inverse (map f (glue D c))))))
