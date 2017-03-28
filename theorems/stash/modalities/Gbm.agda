{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import Orthogonality
open import Modalities
open import FiberedPushout

module Gbm where

  module _ {ℓ} (X Y : Type ℓ) (Z : X → Y → Type ℓ) (M : Modality {ℓ}) where

    open Modality M
    
    f : X → Type ℓ
    f x = Σ Y (λ y → Z x y)

    g : Y → Type ℓ
    g y = Σ X (λ x → Z x y)

    -- The hypothesis of the generalized theorem works out to the following,
    -- which asserts that the fiberwise join of the diagonals of f and g
    -- is in fact an equivalence after applying the modality
    
    hypothesis' : Type ℓ
    hypothesis' = {x₀ x₁ : X} → (p : x₀ == x₁) → (α : f x₀) → (β : f x₁) →
                  {y₀ y₁ : Y} → (q : y₀ == y₁) → (γ : g y₀) → (δ : g y₁) →
                  is-contr (◯ ((α == β [ f ↓ p ]) * (γ == δ [ g ↓ q ])))

    hypothesis : Type ℓ
    hypothesis = {x₀ : X} {y₀ : Y} {z₀ : Z x₀ y₀}  -- This says we are over Z
                 {x₁ : X} {z₁ : Z x₁ y₀}           -- An element of Z×YZ
                 {y₁ : Y} {z₂ : Z x₀ y₁}           -- An element of Z×XZ
                 → is-contr (◯ (Σ (x₀ == x₁) (λ p → z₀ == z₁ [ _ ↓ p ])
                               * Σ (y₀ == y₁) (λ p → z₀ == z₂ [ _ ↓ p ])))

    -- The hope is that the more complicated versions above can be reduced
    -- to the following more elegant one:

    hypothesis'' : Type ℓ
    hypothesis'' = {x₀ : X} {y₀ : Y} → (α : f x₀) → (β : g y₀)
                   → is-contr (◯ ((α == α) * (β == β)))


    W : Type ℓ
    W = FiberedPushout Z

    gap-lcl : {x : X} {y : Y} → Z x y → in-left {P = Z} x == in-right y
    gap-lcl {x} {y} z = ! (glue-left z) ∙ glue-right z

    module OverZ {x₀ : X} {y₀ : Y} {z₀ : Z x₀ y₀} where
      
      -- Here are our total spaces in the first step, passing
      -- the the slice over Z

      X×WZ : Type ℓ
      X×WZ = Σ X (λ x → in-mid {P = Z} z₀ == in-left x)

      Y×WZ : Type ℓ
      Y×WZ = Σ Y (λ y → in-mid {P = Z} z₀ == in-right y)

      Z×WZ : Type ℓ
      Z×WZ = Σ X (λ x → Σ Y (λ y → Σ (Z x y) (λ z → in-mid {P = Z} z₀ == in-mid z)))

      --
      --  Here we start to better isolate the hypothesies of the theorem.
      --  We start with the X side
      --
      
      Z×XZ : Type ℓ
      Z×XZ = Σ X (λ x → Σ Y (λ y → Σ (Z x y) (λ z → x == x₀)))

      -- This type is equivalent to the one above by path induction
      Z×XZ' : Type ℓ
      Z×XZ' = Σ Y (λ y → Z x₀ y) 

      f' : Z×XZ' → Type ℓ
      f' (y , z) = Σ (y == y₀) (λ p → z == z₀ [ (λ y → Z x₀ y) ↓ p ])

      --
      --  Now we do the Y side
      --

      Z×YZ : Type ℓ
      Z×YZ = Σ X (λ x → Σ Y (λ y → Σ (Z x y) (λ z → y == y₀)))

      -- Similarly for this one
      Z×YZ' : Type ℓ
      Z×YZ' = Σ X (λ x → Z x y₀)

      g' : Z×YZ' → Type ℓ
      g' (x , z) = Σ (x == x₀) (λ p → z == z₀ [ (λ x → Z x y₀) ↓ p ])

      -- Okay.  Good.  I claim the total space of each of these is
      -- contractible.

      claim : is-contr (Σ Z×YZ' g')
      claim = ((x₀ , z₀) , (idp , idp)) , (λ { ((.x₀ , .z₀) , idp , idp) → idp })

      -- Right.  In other words, it's equivalent to Z as desired.

      new-hypothesis : Type ℓ
      new-hypothesis = (α : Z×XZ') → (β : Z×YZ') → is-contr (◯ (f' α * g' β))

      pt₀ : Z×XZ
      pt₀ = x₀ , (y₀ , (z₀ , idp))

      pt₁ : Z×YZ
      pt₁ = x₀ , (y₀ , (z₀ , idp))

      gluel₀ : {x : X} → Z x y₀ → in-mid {P = Z} z₀ == in-left x
      gluel₀ z = glue-right z₀ ∙ ! (gap-lcl z) 

      gluer₀ : {y : Y} → Z x₀ y → in-mid {P = Z} z₀ == in-right y
      gluer₀ z = glue-left z₀ ∙ gap-lcl z 

      CodesFor : (w : W) (p : in-mid z₀ == w) → Type ℓ
      CodesFor = FiberedPushoutElim.f _
                   (λ x α → ◯ (hfiber gluel₀ α))
                   (λ x y α → {!!})
                   (λ y α → ◯ (hfiber gluer₀ α))
                   {!!}
                   {!!}

    -- So the real theorem would be about the total map, but this should suffice
    -- by standard kind of stuff
    thm : {x : X} {y : Y} → hypothesis' → (p : in-left x == in-right y) → is-contr (◯ (hfiber gap-lcl p))
    thm = {!!}
    


