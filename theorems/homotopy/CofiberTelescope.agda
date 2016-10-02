{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.TwoPushouts

{-
     f        g
  A ---> B --------> C 
  |      |           |
  v      v   inner   v
  * -> Cof f -> Cof (g ∘ f)
         |           |
         v           v
         * ------> Cof g ≃ Cof inner

-}

module homotopy.CofiberTelescope where

module CofiberOfCofiber {i j k}
  {A : Type i} {B : Type j} {C : Type k} (f : A → B) (g : B → C) where

  corner-span : Span
  corner-span = span (Cofiber f) C B (cfcod' f) g

  private
    top-pushouts-econv : Cofiber (g ∘ f) ≃ Pushout corner-span
    top-pushouts-econv = rsplit-pushouts-equiv (λ _ → tt) f g

  inner : Cofiber f → Cofiber (g ∘ f)
  inner = <– top-pushouts-econv ∘ left {d = corner-span}

  private
    cofiber-span-equiv : SpanEquiv (cofiber-span (left {d = corner-span}))
                                   (cofiber-span inner)
    cofiber-span-equiv = ( span-map (idf _) (<– top-pushouts-econv) (idf _)
                            (comm-sqr λ _ → idp) (comm-sqr λ _ → idp)
                        , idf-is-equiv _ , snd (top-pushouts-econv ⁻¹) , idf-is-equiv _)

  split-equiv : Cofiber g ≃ Cofiber inner
  split-equiv = Pushout-emap cofiber-span-equiv ∘e lsplit-pushouts-equiv cfcod (λ _ → tt) g
