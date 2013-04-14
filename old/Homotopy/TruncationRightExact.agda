{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.PushoutDef
open import Homotopy.PushoutUP as PushoutUP
open import Homotopy.Truncation
open import Homotopy.PullbackDef
open import Homotopy.PullbackInvariantEquiv

module Homotopy.TruncationRightExact {i} (n : ℕ₋₂) (d : pushout-diag i) where

open pushout-diag d
open import Homotopy.PushoutIsPushout d

τd : pushout-diag i
τd = diag (τ n A), (τ n B), (τ n C), (τ-fmap f), (τ-fmap g)

module H  = PushoutUP d  (cst unit)
module τH = PushoutUP τd (is-truncated n)

-- I want to prove that [τ n d.pushout] is a pushout in [is-truncated n]. It
-- first needs to be equipped with a cocone

cocone-τpushout : τH.cocone (τ n (pushout d))
cocone-τpushout = (τ-fmap left , τ-fmap right ,
                     τ-extend ⦃ λ _ → ≡-is-truncated _ (τ-is-truncated _ _) ⦄
                       (ap proj ◯ glue))

-- We have a map [(τ n (pushout d) → E) → τH.cocone E] with [E] in [P] given by
-- [τH.compose-cocone-map] and we want to prove that it’s an equivalence

-- The idea is that it’s the composite of five equivalences:

-- [equiv1 : τ n (pushout d) → E ≃ (pushout d) → E]
--    by the universal property of truncations
-- [equiv2 : (pushout d) → E ≃ H.cocone E]
--    by the universal property of pushout in Type
-- [equiv3 : H.cocone E ≃ pullback … (without truncations)]
--    via [cocone-is-pullback]
-- [equiv4 : pullback … (without truncations) ≃ pullback … (with truncations)]
--    by the universal property of truncations and invariance of pullback wrt
--    equivalence of diagrams
-- [equiv5 : pullback … (with truncations) ≃ τH.cocone E]
--    via [cocone-is-pullback]

module _ (E : Set i) ⦃ P-E : is-truncated n E ⦄ where

  private
    ≡E-is-truncated#instance : {x y : E} → is-truncated n (x ≡ y)
    ≡E-is-truncated#instance = ≡-is-truncated n P-E

    λ-≡E-is-truncated#instance : {A : Set i} {u v : A → E}
      → ((x : A) → is-truncated n (u x ≡ v x))
    λ-≡E-is-truncated#instance = λ _ → ≡E-is-truncated#instance

    ≡≡E-is-truncated#instance : {x y : E} {p q : x ≡ y} → is-truncated n (p ≡ q)
    ≡≡E-is-truncated#instance = ≡-is-truncated n (≡-is-truncated n P-E)

    λ-≡≡E-is-truncated#instance : {A : Set i} {x y : A → E}
      {p q : (a : A) → x a ≡ y a} → ((a : A) → is-truncated n (p a ≡ q a))
    λ-≡≡E-is-truncated#instance = λ _ → ≡≡E-is-truncated#instance

    equiv1 : (τ n (pushout d) → E) ≃ (pushout d → E)
    equiv1 = ((λ u → u ◯ proj) , τ-up n _ _)

    equiv2 : (pushout d → E) ≃ H.cocone E
    equiv2 = ((λ f → ((f ◯ left) , (f ◯ right) , (ap f ◯ glue)))
             , pushout-is-pushout E)

    -- (could be defined more generally somewhere else)
    diag-hom : pullback-diag i
    diag-hom = diag (A → E), (B → E), (C → E), (λ u → u ◯ f), (λ u → u ◯ g)

    τdiag-hom : pullback-diag i
    τdiag-hom = diag (τ n A → E), (τ n B → E), (τ n C → E),
                     (λ u → u ◯ τ-fmap f) , (λ u → u ◯ τ-fmap g)

    equiv3 : H.cocone E ≃ pullback diag-hom
    equiv3 = H.cocone-equiv-pullback E

    p₀ : (a : A → E) (x : τ n C)
      → τ-extend-nondep a (τ-fmap f x) ≡ τ-extend-nondep (a ◯ f) x
    p₀ a = τ-extend (λ x → refl)

    p : (a : A → E) → (τ-extend-nondep a) ◯ τ-fmap f ≡ τ-extend-nondep (a ◯ f)
    p a = funext (p₀ a)

    q₀ : (b : B → E) (x : τ n C)
      → τ-extend-nondep (b ◯ g) x ≡ τ-extend-nondep b (τ-fmap g x)
    q₀ b = τ-extend (λ x → refl)

    q : (b : B → E) → τ-extend-nondep (b ◯ g) ≡ (τ-extend-nondep b) ◯ τ-fmap g
    q b = funext (q₀ b)

    equiv4 : pullback diag-hom ≃ pullback τdiag-hom
    equiv4 = pullback-invariant-equiv diag-hom τdiag-hom
               (τ-extend-equiv n A E) (τ-extend-equiv n B E)
               (τ-extend-equiv n C E) p q

    equiv5 : pullback τdiag-hom ≃ τH.cocone E
    equiv5 = τH.pullback-equiv-cocone E

    -- We have defined the five equivalences, now we want to prove that the
    -- composite is what we want. We start by computing the composite of the
    -- equivalences 3, 4 and 5.

    map-543 : H.cocone E → τH.cocone E
    map-543 (a , b , e) = (τ-extend-nondep a , τ-extend-nondep b , τ-extend e)

    map-543-correct : (x : H.cocone E)
      → equiv5 ☆ (equiv4 ☆ (equiv3 ☆ x)) ≡ map-543 x
    map-543-correct (a , b , h) =
      ap (λ u → _ , _ , u)
        (funext (τ-extend
          (λ x →
            ap-concat (λ u → u (proj x)) (p a)
              (ap τ-extend-nondep (funext h) ∘ q b)
            ∘ (whisker-right _ (happly (happly-funext (p₀ a)) (proj x))
            ∘ (ap-concat (λ u → u (proj x))
                (ap τ-extend-nondep (funext h)) (q b)
            ∘ (whisker-right _
                (compose-ap (λ u → u (proj x)) τ-extend-nondep (funext h))
            ∘ (whisker-right _ (happly (happly-funext h) x)
            ∘ (whisker-left (h x)
                (happly (happly-funext (q₀ b)) (proj x))
            ∘ refl-right-unit (h x)))))))))

    -- We now study the full composite

    map-54321 : (τ n (pushout d) → E) → τH.cocone E
    map-54321 = τH.compose-cocone-map _ _ cocone-τpushout

    map-21-A₀ : (f : τ n (pushout d) → E) (u : τ n A)
      → τH.A→top (map-543 (equiv2 ☆ (equiv1 ☆ f))) u ≡ τH.A→top (map-54321 f) u
    map-21-A₀ f = τ-extend (λ x → refl)

    map-21-A : (f : τ n (pushout d) → E)
      → τH.A→top (map-543 (equiv2 ☆ (equiv1 ☆ f))) ≡ τH.A→top (map-54321 f)
    map-21-A f = funext (map-21-A₀ f)

    map-21-B₀ : (f : τ n (pushout d) → E) (u : τ n B)
      → τH.B→top (map-543 (equiv2 ☆ (equiv1 ☆ f))) u ≡ τH.B→top (map-54321 f) u
    map-21-B₀ f = τ-extend (λ x → refl)

    map-21-B : (f : τ n (pushout d) → E)
      → τH.B→top (map-543 (equiv2 ☆ (equiv1 ☆ f))) ≡ τH.B→top (map-54321 f)
    map-21-B f = funext (map-21-B₀ f)

    map-21-correct : (h : τ n (pushout d) → E)
      → map-543 (equiv2 ☆ (equiv1 ☆ h)) ≡ map-54321 h
    map-21-correct h = τH.cocone-eq _ (map-21-A h) (map-21-B h)
      (τ-extend
        (λ x →
          whisker-right _ (happly (happly-funext (map-21-A₀ h)) (proj (f x)))
          ∘ (compose-ap h proj _
          ∘ (! (refl-right-unit (ap (h ◯ proj) (glue x)))
          ∘ whisker-left (ap (h ◯ proj) (glue x))
          (! (happly (happly-funext (map-21-B₀ h)) (proj (g x))))))))

    map-54321-correct : (f : τ n (pushout d) → E)
      → equiv5 ☆ (equiv4 ☆ (equiv3 ☆ (equiv2 ☆ (equiv1 ☆ f)))) ≡ map-54321 f
    map-54321-correct f = map-543-correct (equiv2 ☆ (equiv1 ☆ f))
                          ∘ map-21-correct f

  map-54321-is-equiv : is-equiv map-54321
  map-54321-is-equiv =
    transport is-equiv (funext map-54321-correct)
      (compose-is-equiv
        ((λ f₁ → equiv4 ☆ (equiv3 ☆ (equiv2 ☆ (equiv1 ☆ f₁))))
        , compose-is-equiv
          ((λ f₁ → equiv3 ☆ (equiv2 ☆ (equiv1 ☆ f₁)))
            , compose-is-equiv
              ((λ f₁ → equiv2 ☆ (equiv1 ☆ f₁))
                , compose-is-equiv equiv1 equiv2)
              equiv3)
          equiv4)
      equiv5)

abstract
  τpushout-is-pushout : τH.is-pushout (τ n (pushout d)) cocone-τpushout
  τpushout-is-pushout E = map-54321-is-equiv E
