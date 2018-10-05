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

  ⊙SphereS-endo-group-structure : ∀ n → GroupStructure (⊙Sphere-endo (S n))
  ⊙SphereS-endo-group-structure n = Susp⊙→-group-structure (⊙Sphere n) (⊙Sphere (S n))

{-
  ⊙LiftSphereS-endo-group-structure : ∀ {i} n → GroupStructure (⊙LiftSphere-endo {i} (S n))
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
-}

  Trunc-⊙SphereS-endo-group : ∀ n → Group₀
  Trunc-⊙SphereS-endo-group n = Trunc-Susp⊙→-group (⊙Sphere n) (⊙Sphere (S n))

{-
  Trunc-⊙LiftSphereS-endo-group : ∀ {i} n → Group i
  Trunc-⊙LiftSphereS-endo-group {i} n = Trunc-LiftSusp⊙→-group {j = i} (⊙Sphere n) (⊙Lift {j = i} (⊙Sphere (S n)))
-}

  Trunc-⊙SphereS-endo-⊙group : ∀ n → ⊙Group₀
  Trunc-⊙SphereS-endo-⊙group n = ⊙[ Trunc-⊙SphereS-endo-group n , [ ⊙idf _ ] ]ᴳ

{-
  Trunc-⊙LiftSphereS-endo-⊙group : ∀ {i} n → ⊙Group i
  Trunc-⊙LiftSphereS-endo-⊙group {i} n = ⊙[ Trunc-⊙LiftSphereS-endo-group {i = i} n , [ ⊙idf _ ] ]ᴳ
-}

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
    Trunc-⊙SphereS-endo-Susp-fmap-iso n , ap [_] (⊙Susp-fmap-idf (Sphere (S n)))

  Trunc-⊙SphereS-endo-⊙group-is-infinite-cyclic : ∀ n → is-infinite-cyclic (Trunc-⊙SphereS-endo-⊙group n)
  Trunc-⊙SphereS-endo-⊙group-is-infinite-cyclic O = Trunc-⊙S¹-endo-⊙group-is-infinite-cyclic
  Trunc-⊙SphereS-endo-⊙group-is-infinite-cyclic (S n) =
    isomorphism-preserves-infinite-cyclic
      (Trunc-⊙SphereS-endo-Susp-fmap-⊙iso n)
      (Trunc-⊙SphereS-endo-⊙group-is-infinite-cyclic n)

{-
  Trunc-⊙SphereS-endo-iso-Trunc-⊙LiftSphereS-endo : ∀ {i} n →
    Trunc-⊙SphereS-endo-group n ≃ᴳ Trunc-⊙LiftSphereS-endo-group {i} n
  Trunc-⊙SphereS-endo-iso-Trunc-⊙LiftSphereS-endo {i} n =
    Trunc-group-emap (⊙SphereS-endo-siso-⊙LiftSphereS-endo {i} n)

  Trunc-⊙SphereS-endo-⊙iso-Trunc-⊙LiftSphereS-endo : ∀ {i} n →
    Trunc-⊙SphereS-endo-⊙group n ⊙≃ᴳ Trunc-⊙LiftSphereS-endo-⊙group {i} n
  Trunc-⊙SphereS-endo-⊙iso-Trunc-⊙LiftSphereS-endo {i} n =
    Trunc-⊙SphereS-endo-iso-Trunc-⊙LiftSphereS-endo {i} n , idp

  Trunc-⊙LiftSphereS-endo-⊙group-is-infinite-cyclic : ∀ {i} n → is-infinite-cyclic (Trunc-⊙LiftSphereS-endo-⊙group {i} n)
  Trunc-⊙LiftSphereS-endo-⊙group-is-infinite-cyclic {i} n =
    isomorphism-preserves-infinite-cyclic
      (Trunc-⊙SphereS-endo-⊙iso-Trunc-⊙LiftSphereS-endo {i} n)
      (Trunc-⊙SphereS-endo-⊙group-is-infinite-cyclic n)
-}

  {- definition of degree -}

  Trunc-⊙SphereS-endo-degree : ∀ n → Trunc-⊙Sphere-endo (S n) → ℤ
  Trunc-⊙SphereS-endo-degree n = is-equiv.g (Trunc-⊙SphereS-endo-⊙group-is-infinite-cyclic n)

  abstract
    Trunc-⊙SphereS-endo-degree-Susp : ∀ n f
      →  Trunc-⊙SphereS-endo-degree (S n) (Trunc-fmap (⊙Susp-fmap ∘ fst) f)
      == Trunc-⊙SphereS-endo-degree n f
    Trunc-⊙SphereS-endo-degree-Susp n f =
      ap (Trunc-⊙SphereS-endo-degree n) (GroupIso.g-f (Trunc-⊙SphereS-endo-Susp-fmap-iso n) f)

  ⊙SphereS-endo-degree : ∀ n → ⊙Sphere-endo (S n) → ℤ
  ⊙SphereS-endo-degree n = Trunc-⊙SphereS-endo-degree n ∘ [_]

  abstract
    ⊙SphereS-endo-degree-Susp : ∀ n f
      →  ⊙SphereS-endo-degree (S n) (⊙Susp-fmap (fst f))
      == ⊙SphereS-endo-degree n f
    ⊙SphereS-endo-degree-Susp n f = Trunc-⊙SphereS-endo-degree-Susp n [ f ]

    ⊙SphereS-endo-degree-Susp' : ∀ n f
      →  ⊙SphereS-endo-degree (S n) (⊙Susp-fmap f)
      == Trunc-⊙SphereS-endo-degree n (Trunc-⊙SphereS-endo-in n [ f ])
    ⊙SphereS-endo-degree-Susp' n f =
      ⊙SphereS-endo-degree (S n) (⊙Susp-fmap f)
        =⟨ ap
            (Trunc-⊙SphereS-endo-degree (S n) ∘ Trunc-fmap ⊙Susp-fmap)
            (! $ is-equiv.f-g (Trunc-⊙SphereS-endo-out-is-equiv n) [ f ]) ⟩
      Trunc-⊙SphereS-endo-degree (S n) (Trunc-fmap ⊙Susp-fmap (Trunc-fmap fst (Trunc-⊙SphereS-endo-in n [ f ])))
        =⟨ ap (Trunc-⊙SphereS-endo-degree (S n))
              (Trunc-fmap-∘ ⊙Susp-fmap fst (Trunc-⊙SphereS-endo-in n [ f ])) ⟩
      Trunc-⊙SphereS-endo-degree (S n) (Trunc-fmap (⊙Susp-fmap ∘ fst) (Trunc-⊙SphereS-endo-in n [ f ]))
        =⟨ Trunc-⊙SphereS-endo-degree-Susp n (Trunc-⊙SphereS-endo-in n [ f ]) ⟩
      Trunc-⊙SphereS-endo-degree n (Trunc-⊙SphereS-endo-in n [ f ])
        =∎

    ⊙SphereS-endo-degree-base-indep : ∀ n {f g}
      → fst f ∼ fst g
      → ⊙SphereS-endo-degree n f == ⊙SphereS-endo-degree n g
    ⊙SphereS-endo-degree-base-indep n {f} {g} f∼g =
      ! (⊙SphereS-endo-degree-Susp n f)
      ∙ ap (λ f → ⊙SphereS-endo-degree (S n) (Susp-fmap f , idp)) (λ= f∼g)
      ∙ ⊙SphereS-endo-degree-Susp n g

{-
  Trunc-⊙LiftSphereS-endo-degree : ∀ {i} n → Trunc-⊙LiftSphere-endo {i} (S n) → ℤ
  Trunc-⊙LiftSphereS-endo-degree {i} n = is-equiv.g (Trunc-⊙LiftSphereS-endo-⊙group-is-infinite-cyclic {i} n)

  abstract
    Trunc-⊙LiftSphereS-endo-degree-Susp : ∀ {i} n f
      →  Trunc-⊙LiftSphereS-endo-degree {i} (S n) (Trunc-fmap (λ f → ⊙Lift-fmap (⊙Susp-fmap (⊙lower ⊙∘ f ⊙∘ ⊙lift))) f)
      == Trunc-⊙LiftSphereS-endo-degree {i} n f
    Trunc-⊙LiftSphereS-endo-degree-Susp {i} n =
      Trunc-elim
        {{λ _ → =-preserves-level ℤ-is-set}}
        (λ f → ⊙SphereS-endo-degree-Susp n (⊙lower ⊙∘ f ⊙∘ ⊙lift))

  ⊙LiftSphereS-endo-degree : ∀ {i} n → ⊙LiftSphere-endo {i} (S n) → ℤ
  ⊙LiftSphereS-endo-degree {i} n = Trunc-⊙LiftSphereS-endo-degree {i} n ∘ [_]

  abstract
    ⊙LiftSphereS-endo-degree-Susp : ∀ {i} n f
      →  ⊙LiftSphereS-endo-degree {i} (S n) (⊙Lift-fmap (⊙Susp-fmap (⊙lower ⊙∘ f ⊙∘ ⊙lift)))
      == ⊙LiftSphereS-endo-degree {i} n f
    ⊙LiftSphereS-endo-degree-Susp {i} n f =
      Trunc-⊙LiftSphereS-endo-degree-Susp {i} n [ f ]

    ⊙LiftSphereS-endo-degree-base-indep : ∀ {i} n {f g}
      → fst f ∼ fst g
      → ⊙LiftSphereS-endo-degree {i} n f == ⊙LiftSphereS-endo-degree {i} n g
    ⊙LiftSphereS-endo-degree-base-indep {i} n {f} {g} f∼g =
      ! (⊙LiftSphereS-endo-degree-Susp {i} n f)
      ∙ ap (λ f → ⊙LiftSphereS-endo-degree {i} (S n) (⊙Lift-fmap (Susp-fmap (lower ∘ f ∘ lift) , idp))) (λ= f∼g)
      ∙ ⊙LiftSphereS-endo-degree-Susp {i} n g
-}
