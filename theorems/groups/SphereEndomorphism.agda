{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.LoopSpaceCircle
open import homotopy.PinSn
open import homotopy.SphereEndomorphism
open import homotopy.SuspAdjointLoop
open import groups.FromSusp
open import groups.Int
open import groups.Pointed
open import groups.SuspAdjointLoop
open import groups.ToOmega

module groups.SphereEndomorphism where

  Trunc-⊙SphereS-endo-group : ∀ n → Group₀
  Trunc-⊙SphereS-endo-group n = Trunc-Susp⊙→-group (⊙Sphere n) (⊙Sphere (S n))

  Trunc-⊙SphereS-endo-⊙group : ∀ n → ⊙Group₀
  Trunc-⊙SphereS-endo-⊙group n = ⊙[ Trunc-⊙SphereS-endo-group n , [ ⊙idf _ ] ]ᴳ

  Trunc-⊙S¹-endo-group-iso-ℤ : Trunc-⊙SphereS-endo-group 0 ≃ᴳ ℤ-group
  Trunc-⊙S¹-endo-group-iso-ℤ =
    Trunc-⊙SphereS-endo-group 0
      ≃ᴳ⟨ Trunc-Susp⊙→-iso-Trunc-⊙→Ω ⊙Bool ⊙S¹ ⟩
    Trunc-⊙→Ω-group ⊙Bool ⊙S¹
      ≃ᴳ⟨ Trunc-⊙Bool→Ω-iso-π₁ ⊙S¹ ⟩
    πS 0 ⊙S¹
      ≃ᴳ⟨ πS-SphereS-iso-ℤ 0 ⟩
    ℤ-group
      ≃ᴳ∎

  Trunc-⊙S¹-endo-⊙group-iso-⊙ℤ : Trunc-⊙SphereS-endo-⊙group 0 ⊙≃ᴳ ℤ-⊙group
  Trunc-⊙S¹-endo-⊙group-iso-⊙ℤ = Trunc-⊙S¹-endo-group-iso-ℤ ,
    equiv-adj' ΩS¹-equiv-ℤ {a = ap (idf _) loop} {b = 1} (ap-idf loop)

  Trunc-⊙S¹-endo-⊙group-is-infinite-cyclic : is-infinite-cyclic (Trunc-⊙SphereS-endo-⊙group 0)
  Trunc-⊙S¹-endo-⊙group-is-infinite-cyclic =
    isomorphism-preserves'-infinite-cyclic Trunc-⊙S¹-endo-⊙group-iso-⊙ℤ ℤ-is-infinite-cyclic

  Trunc-⊙SphereS-endo-Susp-fmap-iso :
    ∀ n → Trunc-⊙SphereS-endo-group n ≃ᴳ Trunc-⊙SphereS-endo-group (S n)
  Trunc-⊙SphereS-endo-Susp-fmap-iso n =
    Trunc-group-fmap (Susp⊙→-Susp-fmap-shom (⊙Sphere n) (⊙Sphere (S n))) ,
    Trunc-⊙SphereS-endo-Susp-is-equiv n

  Trunc-⊙SphereS-endo-Susp-fmap-⊙iso :
    ∀ n → Trunc-⊙SphereS-endo-⊙group n ⊙≃ᴳ Trunc-⊙SphereS-endo-⊙group (S n)
  Trunc-⊙SphereS-endo-Susp-fmap-⊙iso n =
    Trunc-⊙SphereS-endo-Susp-fmap-iso n , ap [_] (⊙Susp-fmap-idf (⊙Sphere (S n)))

  Trunc-⊙SphereS-endo-⊙group-is-infinite-cyclic : ∀ n → is-infinite-cyclic (Trunc-⊙SphereS-endo-⊙group n)
  Trunc-⊙SphereS-endo-⊙group-is-infinite-cyclic O = Trunc-⊙S¹-endo-⊙group-is-infinite-cyclic
  Trunc-⊙SphereS-endo-⊙group-is-infinite-cyclic (S n) =
    isomorphism-preserves-infinite-cyclic
      (Trunc-⊙SphereS-endo-Susp-fmap-⊙iso n)
      (Trunc-⊙SphereS-endo-⊙group-is-infinite-cyclic n)
