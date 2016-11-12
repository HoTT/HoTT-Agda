{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.CircleHSpace
open import homotopy.LoopSpaceCircle
open import homotopy.Pi2HSusp
open import homotopy.IterSuspensionStable

-- This summerizes all [πₙ Sⁿ]
module homotopy.PinSn where

  -- TODO
  -- The lemmas about [loop^] should be generalized to generic exponential
  -- functions, and then these lemmas are just special cases on loop spaces.

  private
    -- another way is to use path induction to prove the other direction,
    -- but personally I do not feel it is easier.
    abstract
      -- proved in LoopSpaceCircle
      -- loop^succ : ∀ (z : ℤ) → loop^ z ∙ loop == loop^ (succ z)

      -- mimicking [loop^pred]
      loop^pred : ∀ (z : ℤ) → loop^ z ∙ ! loop == loop^ (pred z)
      loop^pred (negsucc n) = idp
      loop^pred (pos O) = idp
      loop^pred (pos (S n)) =
        (loop^ (pos n) ∙ loop) ∙ ! loop
          =⟨ ∙-assoc (loop^ (pos n)) loop (! loop) ⟩
        loop^ (pos n) ∙ (loop ∙ ! loop)
          =⟨ !-inv-r loop |in-ctx loop^ (pos n) ∙_ ⟩
        loop^ (pos n) ∙ idp
          =⟨ ∙-unit-r $ loop^ (pos n) ⟩
        loop^ (pos n)
          ∎

      -- because of how [loop^] is defined,
      -- it is easier to prove the swapped version
      loop^-ℤ+' : ∀ (z₁ z₂ : ℤ) →
        loop^ (z₁ ℤ+ z₂) == loop^ z₂ ∙ loop^ z₁
      loop^-ℤ+' (pos O) z₂ = ! $ ∙-unit-r (loop^ z₂)
      loop^-ℤ+' (pos (S n₁)) z₂ =
        loop^ (succ (pos n₁ ℤ+ z₂))
          =⟨ ! $ loop^succ (pos n₁ ℤ+ z₂) ⟩
        loop^ (pos n₁ ℤ+ z₂) ∙ loop
          =⟨ loop^-ℤ+' (pos n₁) z₂ |in-ctx _∙ loop ⟩
        (loop^ z₂ ∙ loop^ (pos n₁)) ∙ loop
          =⟨ ∙-assoc (loop^ z₂) (loop^ (pos n₁)) loop ⟩
        loop^ z₂ ∙ (loop^ (pos n₁) ∙ loop)
          ∎
      loop^-ℤ+' (negsucc O) z₂ = ! $ loop^pred z₂
      loop^-ℤ+' (negsucc (S n₁)) z₂ =
        loop^ (pred (negsucc n₁ ℤ+ z₂))
          =⟨ ! $ loop^pred (negsucc n₁ ℤ+ z₂) ⟩
        loop^ (negsucc n₁ ℤ+ z₂) ∙ ! loop
          =⟨ loop^-ℤ+' (negsucc n₁) z₂ |in-ctx _∙ ! loop ⟩
        (loop^ z₂ ∙ loop^ (negsucc n₁)) ∙ ! loop
          =⟨ ∙-assoc (loop^ z₂) (loop^ (negsucc n₁)) (! loop) ⟩
        loop^ z₂ ∙ (loop^ (negsucc n₁) ∙ ! loop)
          ∎

    loop^-ℤ+ : ∀ (z₁ z₂ : ℤ) →
      loop^ (z₁ ℤ+ z₂) == loop^ z₁ ∙ loop^ z₂
    loop^-ℤ+ z₁ z₂ = ap loop^ (ℤ+-comm z₁ z₂) ∙ loop^-ℤ+' z₂ z₁

    ℤ-iso-π1S¹ : ℤ-group ≃ᴳ πS 0 ⊙S¹
    ℤ-iso-π1S¹ = ≃-to-≃ᴳ
      (unTrunc-equiv (Ω^ 1 ⊙S¹) (ΩS¹-is-set base) ⁻¹ ∘e ΩS¹≃ℤ ⁻¹)
      (λ z₁ z₂ → ap [_] $ loop^-ℤ+ z₁ z₂)

  private
    πS-SphereS'-iso-ℤ : ∀ n → πS n (⊙Susp^ n ⊙S¹) ≃ᴳ ℤ-group
    πS-SphereS'-iso-ℤ 0 = ℤ-iso-π1S¹ ⁻¹ᴳ
    πS-SphereS'-iso-ℤ 1 =
      πS 1 ⊙S²
        ≃ᴳ⟨ Pi2HSusp.π₂-Susp S¹-level S¹-conn ⊙S¹-hSpace ⟩
      πS 0 ⊙S¹
        ≃ᴳ⟨ πS-SphereS'-iso-ℤ O ⟩
      ℤ-group
        ≃ᴳ∎
    πS-SphereS'-iso-ℤ (S (S n)) =
      πS (S (S n)) (⊙Susp^ (S (S n)) ⊙S¹)
        ≃ᴳ⟨ Susp^StableSucc.stable ⊙S¹ S¹-conn
             (S n) (S n) (≤-ap-S $ ≤-ap-S $ *2-increasing n) ⟩
      πS (S n) (⊙Susp^ (S n) ⊙S¹)
        ≃ᴳ⟨ πS-SphereS'-iso-ℤ (S n) ⟩
      ℤ-group
        ≃ᴳ∎

  πS-SphereS-iso-ℤ : ∀ n → πS n (⊙Sphere (S n)) ≃ᴳ ℤ-group
  πS-SphereS-iso-ℤ n = πS-SphereS'-iso-ℤ n
                   ∘eᴳ πS-emap n (⊙Susp^-Susp-split-iso n ⊙S⁰)
