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

  ⊙SphereS-endo-group-structure : ∀ n → GroupStructure (⊙Sphere (S n) ⊙→ ⊙Sphere (S n))
  ⊙SphereS-endo-group-structure n = Susp⊙→-group-structure (⊙Sphere n) (⊙Sphere (S n))

  ⊙LiftSphereS-endo-group-structure : ∀ {i} n →
    GroupStructure (⊙Lift {j = i} (⊙Sphere (S n)) ⊙→ ⊙Lift {j = i} (⊙Sphere (S n)))
  ⊙LiftSphereS-endo-group-structure {i} n =
    LiftSusp⊙→-group-structure {j = i} (⊙Sphere n) (⊙Lift {j = i} (⊙Sphere (S n)))

  ⊙SphereS-endo-siso-⊙LiftSphereS-endo : ∀ {i} n →
    ⊙SphereS-endo-group-structure n ≃ᴳˢ ⊙LiftSphereS-endo-group-structure {i} n
  ⊙SphereS-endo-siso-⊙LiftSphereS-endo {i} n = ≃-to-≃ᴳˢ
    ⊙Lift-fmap-equiv
    (λ f g → ap (_⊙∘ ⊙pinch (⊙Sphere n) ⊙∘ ⊙lower {j = i}) $ ! $
      ⊙∨-rec (⊙Lift-fmap f) (⊙Lift-fmap g) ⊙∘ ⊙∨-fmap ⊙lift ⊙lift
        =⟨ ⊙λ= $ ⊙∨-rec-fmap (⊙Lift-fmap f) (⊙Lift-fmap g) ⊙lift ⊙lift ⟩
      ⊙∨-rec (⊙lift ⊙∘ f) (⊙lift ⊙∘ g)
        =⟨ ! $ ⊙λ= $ ⊙∨-rec-post∘ ⊙lift f g ⟩
      ⊙lift ⊙∘ ⊙∨-rec f g
        =∎)

  Trunc-⊙SphereS-endo-group : ∀ n → Group₀
  Trunc-⊙SphereS-endo-group n = Trunc-Susp⊙→-group (⊙Sphere n) (⊙Sphere (S n))

  Trunc-⊙LiftSphereS-endo-group : ∀ {i} n → Group i
  Trunc-⊙LiftSphereS-endo-group {i} n = Trunc-LiftSusp⊙→-group {j = i} (⊙Sphere n) (⊙Lift {j = i} (⊙Sphere (S n)))

  Trunc-⊙SphereS-endo-⊙group : ∀ n → ⊙Group₀
  Trunc-⊙SphereS-endo-⊙group n = ⊙[ Trunc-⊙SphereS-endo-group n , [ ⊙idf _ ] ]ᴳ

  Trunc-⊙LiftSphereS-endo-⊙group : ∀ {i} n → ⊙Group i
  Trunc-⊙LiftSphereS-endo-⊙group {i} n = ⊙[ Trunc-⊙LiftSphereS-endo-group {i = i} n , [ ⊙idf _ ] ]ᴳ

  Trunc-⊙SphereS-endo-iso-Trunc-⊙LiftSphereS-endo : ∀ {i} n →
    Trunc-⊙SphereS-endo-group n ≃ᴳ Trunc-⊙LiftSphereS-endo-group {i} n
  Trunc-⊙SphereS-endo-iso-Trunc-⊙LiftSphereS-endo {i} n =
    Trunc-group-emap (⊙SphereS-endo-siso-⊙LiftSphereS-endo {i} n)

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
