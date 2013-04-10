{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Truncation
open import Homotopy.Connected
open import Spaces.Suspension
open import Homotopy.PushoutDef
import Homotopy.PushoutUP as PushoutUP

-- In this file I prove that if [A] is n-connected and its (n+1)-truncation is
-- inhabited, then [suspension A] is (n+1)-connected.
--
-- The hypothesis that [τ (S n) A] is inhabited is not necessary, it can be
-- removed but it’s simpler to assume it

module Homotopy.ConnectedSuspension
  {i} (A : Set i) {n : ℕ₋₂} (p : is-connected n A) (x₀ : τ (S n) A) where

-- The (n+1)-truncation of the suspension is a pushout of the following diagram

τ-susp-diag : pushout-diag i
τ-susp-diag = diag τ (S n) unit , τ (S n) unit , τ (S n) A
              , τ-extend-nondep (λ _ → proj tt)
              , τ-extend-nondep (λ _ → proj tt)

module τ-susp-H = PushoutUP τ-susp-diag (is-truncated (S n))

import Homotopy.TruncationRightExact (S n) (suspension-diag A) as Exact

abstract
  trunc-cocone : τ-susp-H.cocone (τ (S n) (suspension A))
  trunc-cocone = Exact.cocone-τpushout

  trunc-is-pushout : τ-susp-H.is-pushout (τ (S n) (suspension A)) trunc-cocone
  trunc-is-pushout = Exact.τpushout-is-pushout

-- The previous diagram is equivalent to the following

susp-diag : pushout-diag i
susp-diag = suspension-diag (τ (S n) A)

module susp-H = PushoutUP susp-diag (is-truncated (S n))

-- To be moved
τ-unit-to-unit : τ (S n) (unit {i}) → unit {i}
τ-unit-to-unit _ = tt

abstract
  τ-unit-to-unit-is-equiv : is-equiv τ-unit-to-unit
  τ-unit-to-unit-is-equiv =
    iso-is-eq _ (λ _ → proj tt)
      (λ _ → refl)
      (τ-extend
         ⦃ λ _ → ≡-is-truncated (S n) (τ-is-truncated (S n) _) ⦄
        (λ _ → refl))

τ-unit-equiv-unit : τ (S n) unit ≃ unit
τ-unit-equiv-unit = (τ-unit-to-unit , τ-unit-to-unit-is-equiv)
-- / To be moved

abstract
  τ-susp-equal-susp : τ-susp-diag ≡ susp-diag
  τ-susp-equal-susp = pushout-diag-eq τ-unit-equiv-unit τ-unit-equiv-unit
                        (id-equiv _) (λ _ → refl) (λ _ → refl)

  -- But we prove by hand that the point is also a pushout of this diagram
  unit-cocone : susp-H.cocone unit
  unit-cocone = (id _ susp-H., id _ , cst refl)

  private
    factor-pushout : (E : Set i) → (susp-H.cocone E → (unit {i} → E))
    factor-pushout E c = susp-H.A→top c

    x : {E : Set i} → (susp-H.cocone E → E)
    x c = susp-H.A→top c tt

    y : {E : Set i} → (susp-H.cocone E → E)
    y c = susp-H.B→top c tt

    x≡y : {E : Set i} (c : susp-H.cocone E) → x c ≡ y c
    x≡y c = susp-H.h c x₀

    ττA-is-contr : is-contr (τ n (τ (S n) A))
    ττA-is-contr = equiv-types-truncated _ (τ-equiv-ττ n A) p

  susp-H-unit-is-pushout : susp-H.is-pushout unit unit-cocone
  susp-H-unit-is-pushout E ⦃ P-E ⦄ =
    iso-is-eq _
      (factor-pushout E)
      (λ c →
        susp-H.cocone-eq-raw _ refl (funext (λ _ → x≡y c))
          (app-is-inj x₀ ττA-is-contr (P-E _ _)
            (trans-Π2 _ (λ v _ → susp-H.A→top c tt ≡ v tt)
              (funext (λ r → susp-H.h c x₀)) _ _
              ∘ (trans-cst≡app _ (λ u → u tt) (funext (λ r → susp-H.h c x₀)) _
              ∘ happly (happly-funext (λ _ → susp-H.h c x₀)) tt))))
      (λ _ → refl)

-- Type of (S n)-truncated pushout-diagrams (this should probably be defined
-- more generally in Homotopy.PushoutDef or something)
truncated-diag : Set _
truncated-diag = Σ (pushout-diag i)
                 (λ d → (is-truncated (S n) (pushout-diag.A d))
                        × ((is-truncated (S n) (pushout-diag.B d))
                        × (is-truncated (S n) (pushout-diag.C d))))

τ-susp-trunc-diag : truncated-diag
τ-susp-trunc-diag = (τ-susp-diag , (τ-is-truncated (S n) _ ,
                                     (τ-is-truncated (S n) _ ,
                                      τ-is-truncated (S n) _)))

susp-trunc-diag : truncated-diag
susp-trunc-diag = (susp-diag , (unit-is-truncated-S#instance ,
                               (unit-is-truncated-S#instance ,
                                τ-is-truncated (S n) _)))

-- The two diagrams are equal as truncated diagrams
abstract
  τ-susp-trunc-equal-susp-trunc : τ-susp-trunc-diag ≡ susp-trunc-diag
  τ-susp-trunc-equal-susp-trunc = Σ-eq τ-susp-equal-susp
                (Σ-eq (π₁ (is-truncated-is-prop (S n) _ _))
                (Σ-eq (π₁ (is-truncated-is-prop (S n) _ _))
                (π₁ (is-truncated-is-prop (S n) _ _))))

new-cocone : (d : truncated-diag) → (Set i → Set i)
new-cocone (d , (_ , (_ , _))) =
  PushoutUP.cocone d (is-truncated (S n))

new-is-pushout : (d : truncated-diag)
  → ((D : Set i) ⦃ PD : is-truncated (S n) D ⦄
     (Dcocone : new-cocone d D) → Set _)
new-is-pushout (d , (_ , (_ , _))) =
  PushoutUP.is-pushout d (is-truncated (S n))

unit-new-cocone : (d : truncated-diag) → new-cocone d unit
unit-new-cocone d = ((λ _ → tt) PushoutUP., (λ _ → tt) , (λ _ → refl))

unit-is-pushout : (d : truncated-diag) → Set _
unit-is-pushout d = new-is-pushout d unit (unit-new-cocone d)

abstract
  unit-τ-is-pushout :
    τ-susp-H.is-pushout unit (unit-new-cocone τ-susp-trunc-diag)
  unit-τ-is-pushout =
    transport unit-is-pushout (! τ-susp-trunc-equal-susp-trunc)
              susp-H-unit-is-pushout

private
  unit-equiv-τSnΣA : unit {i} ≃ τ (S n) (suspension A)
  unit-equiv-τSnΣA =
    τ-susp-H.pushout-equiv-pushout
      unit   (unit-new-cocone τ-susp-trunc-diag) unit-τ-is-pushout
      (τ (S n) (suspension A)) trunc-cocone      trunc-is-pushout

abstract
  suspension-is-connected-S : is-connected (S n) (suspension A)
  suspension-is-connected-S =
    equiv-types-truncated _ unit-equiv-τSnΣA unit-is-contr
