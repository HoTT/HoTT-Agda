{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.CircleHSpace
open import homotopy.LoopSpaceCircle
open import homotopy.Pi2HSusp
open import homotopy.IterSuspensionStable

-- This summerizes all [πₙ Sⁿ]
module homotopy.PinSn where

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

    ℤ-to-π₁S¹ : ℤ-group →ᴳ πS 0 ⊙S¹
    ℤ-to-π₁S¹ =
      record { f = [_] ∘ loop^
             ; pres-comp = λ z₁ z₂ → ap [_] $ loop^-ℤ+ z₁ z₂
             }

    ℤ-to-π₁S¹-equiv : ℤ-group ≃ᴳ πS 0 ⊙S¹
    ℤ-to-π₁S¹-equiv = ℤ-to-π₁S¹ , snd (unTrunc-equiv (Ω^ 1 ⊙S¹) (ΩS¹-is-set base) ⁻¹ ∘e ΩS¹≃ℤ ⁻¹)

  π₁S¹ : πS 0 ⊙S¹ == ℤ-group
  π₁S¹ = ! $ group-ua ℤ-to-π₁S¹-equiv

  π₂S² : πS 1 ⊙S² == ℤ-group
  π₂S² =
    πS 1 ⊙S²
      =⟨ Pi2HSusp.π₂-Suspension S¹ S¹-level S¹-connected S¹-hSpace ⟩
    πS 0 ⊙S¹
      =⟨ π₁S¹ ⟩
    ℤ-group
      ∎

  private
    πₙ₊₂Sⁿ⁺² : ∀ n → πS (S n) (⊙Susp^ (S n) ⊙S¹) == ℤ-group
    πₙ₊₂Sⁿ⁺² 0 = π₂S²
    πₙ₊₂Sⁿ⁺² (S n) =
      πS (S (S n)) (⊙Susp^ (S (S n)) ⊙S¹)
        =⟨ Susp^StableSucc.stable ⊙S¹ S¹-connected
             (S n) (S n) (≤-ap-S $ ≤-ap-S $ *2-increasing n) ⟩
      πS (S n) (⊙Susp^ (S n) ⊙S¹)
        =⟨ πₙ₊₂Sⁿ⁺² n ⟩
      ℤ-group
        ∎

    lemma : ∀ n → ⊙Susp^ n ⊙S¹ == ⊙Sphere (S n)
    lemma n = ⊙Susp^-+ n 1 ∙ ap ⊙Sphere (+-comm n 1)

  πₙ₊₁Sⁿ⁺¹ : ∀ n → πS n (⊙Sphere (S n)) == ℤ-group
  πₙ₊₁Sⁿ⁺¹ 0 = π₁S¹
  πₙ₊₁Sⁿ⁺¹ (S n) = ap (πS (S n)) (! $ lemma (S n)) ∙ πₙ₊₂Sⁿ⁺² n
