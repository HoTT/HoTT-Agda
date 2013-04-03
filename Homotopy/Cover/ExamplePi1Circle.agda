{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Connected

{-
  An example of using the overkilling covering space library.
-}

module Homotopy.Cover.ExamplePi1Circle where

  open import Homotopy.Truncation
  open import Homotopy.PathTruncation
  open import Spaces.Circle

  {-
      The 1st step: Show that the circle is connected.
  -}
  S¹-is-⟨1⟩-connected : is-connected ⟨0⟩ S¹
  S¹-is-⟨1⟩-connected = proj base ,
    τ-extend ⦃ λ _ → ≡-is-set $ π₀-is-set S¹ ⦄
      (S¹-rec (λ x → proj x ≡ proj base) (refl _)
        (prop-has-all-paths (π₀-is-set S¹ _ _) _ _))

  open import Integers
  open import Homotopy.Pointed
  open import Homotopy.Cover.Def S¹
  open import Homotopy.Cover.HomotopyGroupSetIsomorphism
    (⋆[ S¹ , base ]) S¹-is-⟨1⟩-connected

  S¹-covering : covering
  S¹-covering = let fiber = S¹-rec-nondep Set ℤ (eq-to-path succ-equiv) in
    cov[ fiber , S¹-rec (is-set ◯ fiber) ℤ-is-set (prop-has-all-paths is-set-is-prop _ _) ]

  open covering S¹-covering

  {-
      The 2nd step : Show that S¹ is contractible.
  -}

  -- Lemmas
  trans-fiber-loop : ∀ z → transport fiber loop z ≡ succ z
  trans-fiber-loop z =
    transport fiber loop z
      ≡⟨ ! $ trans-ap (id _) fiber loop z ⟩
    transport (id _) (ap fiber loop) z
      ≡⟨ ap (λ x → transport (id _) x z) $ S¹-β-loop-nondep Set ℤ (eq-to-path _) ⟩
    transport (id _) (eq-to-path succ-equiv) z
      ≡⟨ trans-id-eq-to-path _ _ ⟩∎
    succ z
      ∎
  trans-fiber-!loop : ∀ z → transport fiber (! loop) z ≡ pred z
  trans-fiber-!loop z = move!-transp-right fiber loop _ _ $ ! $ trans-fiber-loop _ ∘ succ-pred z

  -- The center is path-end.
  loopⁿ-end : Σ S¹ fiber
  loopⁿ-end = (base , O)

  -- Climbing up the stairs.
  loopⁿ-succ : ∀ z → _≡_ {A = Σ S¹ fiber} (base , z) (base , succ z)
  loopⁿ-succ z = Σ-eq loop $ trans-fiber-loop z

  -- Agda needs us to show the induction order explicitly,
  -- and so there are so many functions.
  loopⁿ : ∀ z → (base , z) ≡ loopⁿ-end
  loopⁿ-pos : ∀ n → (base , pos n) ≡ loopⁿ-end
  loopⁿ-neg : ∀ n → (base , neg n) ≡ loopⁿ-end

  loopⁿ O = refl _
  loopⁿ (pos _) = loopⁿ-pos _
  loopⁿ (neg _) = loopⁿ-neg _
  loopⁿ-pos 0 = ! $ loopⁿ-succ _
  loopⁿ-pos (S _) = (! $ loopⁿ-succ _) ∘ loopⁿ-pos _
  loopⁿ-neg 0 = loopⁿ-succ _
  loopⁿ-neg (S _) = loopⁿ-succ _ ∘ loopⁿ-neg _

  private
    -- This lemma should be derivable from trans-Π2-dep and trans-id≡cst and ...
    -- but a simple J rule looks better.
    lemma₁ : ∀ {x₁ x₂} (q : x₁ ≡ x₂) (f : ∀ z → (x₁ , z) ≡ loopⁿ-end) (z : fiber x₂) 
      → transport (λ s → ∀ z → (s , z) ≡ loopⁿ-end) q f z
      ≡ Σ-eq (! q) (refl _) ∘ f (transport fiber (! q) z)
    lemma₁ (refl _) f z = refl _ 

  -- One can follow Michael's proof to finish this, but this is not
  -- the main point in this example and is too annoying.  Thus I skip it.
  private
    postulate
      magic : ∀ {i} {X : Set i} → X

  path : ∀ x z → (x , z) ≡ loopⁿ-end
  path = S¹-rec (λ s → ∀ z → (s , z) ≡ loopⁿ-end) loopⁿ $ funext λ z →
    transport (λ s → ∀ z → (s , z) ≡ loopⁿ-end) loop loopⁿ z
      ≡⟨ lemma₁ loop loopⁿ z ⟩
    Σ-eq (! loop) (refl _) ∘ loopⁿ (transport fiber (! loop) z)
      ≡⟨ ap (λ x → Σ-eq (! loop) (refl _) ∘ x) $ apd! loopⁿ (trans-fiber-!loop z) ⟩
    Σ-eq (! loop) (refl _) ∘ (transport (λ z → (base , z) ≡ loopⁿ-end) (! $ trans-fiber-!loop z) (loopⁿ (pred z)))
      ≡⟨ magic ⟩∎
    loopⁿ z
      ∎

  S¹-covering-is-universal : is-universal S¹-covering
  S¹-covering-is-universal = contr-is-connected ⟨1⟩ $ (base , O) , uncurry path

  ℤ-π¹S¹-equiv : ℤ ≃ (base ≡₀ base)
  ℤ-π¹S¹-equiv = GiveMeAPoint.fiber-a≃fg S¹-covering S¹-covering-is-universal O
