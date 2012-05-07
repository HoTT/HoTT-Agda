{-# OPTIONS --without-K #-}

open import Types
open import Paths
open import Equivalences

module FiberEquivalences {i j k} {A : Set i} {P : A → Set k} {Q : A → Set j} (f : (x : A) → (P x → Q x)) where

-- We want to prove that if [f] induces an equivalence on the total spaces, then [f] induces an equivalence fiberwise

total-map : Σ A P → Σ A Q
total-map (x , y) = (x , f x y)

module TotalMapEquiv (e : is-equiv total-map) where

  total-equiv : Σ A P ≃ Σ A Q
  total-equiv = (total-map , e)

  base-path-inverse : (x : A) (y : Q x) → π₁ ((total-equiv ⁻¹) $ (x , y)) ≡ x
  base-path-inverse x y = base-path (inverse-right-inverse total-equiv (x , y))
  
  total-map-fiberwise-on-paths : {u v : Σ A P} (p : u ≡ v) → base-path (map total-map p) ≡ base-path p
  total-map-fiberwise-on-paths (refl _) = refl _

  inv : ((x : A) → (Q x → P x))
  inv x y = transport P (base-path-inverse x y) (π₂ ((total-equiv ⁻¹) $ (x , y)))
  
  app-trans : {x y : A} (p : x ≡ y) (u : P x)
    → f y (transport P p u) ≡ transport Q p (f x u)
  app-trans (refl _) _ = refl _
  
  inv-right-inverse : (x : A) (y : Q x) → f x (inv x y) ≡ y
  inv-right-inverse x y = app-trans (base-path (inverse-right-inverse total-equiv (x , y))) (π₂ (inverse (_ , e) (x , y)))
    ∘ fiber-path (π₂ (π₁ (e (x , y))))
  
  base-path-opposite : ∀ {i j} {A : Set i} {P : A → Set j} {x y : Σ A P} (p : x ≡ y) → base-path (! p) ≡ ! (base-path p)
  base-path-opposite (refl _) = refl _

  inv-left-inverse : (x : A) (y : P x) → inv x (f x y) ≡ y
  inv-left-inverse x y = map (λ u → transport P (base-path (inverse-right-inverse total-equiv (x , f x y))) u) (lemma2 x y)
    ∘ (! (trans-concat {P = P} (base-path (inverse-right-inverse total-equiv (x , f x y))) (! (base-path-inverse x (f x y))) y)
    ∘ map (λ p → transport P p y) (opposite-left-inverse (map π₁ (π₂ (π₁ (e (x , f x y))))))) where

    lemma1 : (x : A) (y : P x) → base-path-inverse x (f x y) ≡ base-path (inverse-left-inverse total-equiv (x , y))
    lemma1 x y = (map base-path (inverse-triangle total-equiv (x , y)) ∘ total-map-fiberwise-on-paths _)
  
    lemma2 : (x : A) (y : P x) → π₂ ((total-equiv ⁻¹) $ (x , f x y)) ≡ transport P (! (base-path-inverse x (f x y))) y
    lemma2 x y = ! (fiber-path (! (inverse-left-inverse total-equiv (x , y))))
      ∘ map (λ p → transport P p y) (base-path-opposite (inverse-left-inverse total-equiv (x , y)) ∘ ! (map ! (lemma1 x y)))
  
  fiberwise-equiv : ((x : A) → is-equiv (f x))
  fiberwise-equiv x = iso-is-eq (f x) (inv x) (inv-right-inverse x) (inv-left-inverse x)

fiberwise-equiv : is-equiv total-map → ((x : A) → is-equiv (f x))
fiberwise-equiv = TotalMapEquiv.fiberwise-equiv
