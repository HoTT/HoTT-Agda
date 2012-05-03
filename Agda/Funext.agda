{-# OPTIONS --without-K #-}

open import Types
open import Paths
open import Contractible
open import Equivalences
open import Univalence

module Funext where

-- Naive non dependent function extensionality

module FunextNonDep {i j : Level} {A : Set i} {B : Set j} (f g : A → B) (h : (x : A) → f x ≡ g x) where

  private
    equiv-comp : {i j : Level} {A : Set i} {B C : Set j} (f : B ≃ C)
      → is-equiv (λ (g : A → B) → λ (x : A) → f $ (g x))
    equiv-comp {A = A} f = equiv-induction (λ B C f → is-equiv (λ (g : A → B) → λ (x : A) → f $ (g x))) (λ A' y → id-is-equiv (A → A') y) _ _ f

    free-path-space : {i : Level} (A : Set i) → Set _
    free-path-space A = Σ A (λ x → Σ A (λ y → x ≡ y))

    d : A → free-path-space B
    d x = (f x , (f x , refl (f x)))

    e : A → free-path-space B
    e x = (f x , (g x , h x))

    π₁-is-equiv : is-equiv (λ (y : free-path-space B) → π₁ y)
    π₁-is-equiv =
      iso-is-eq π₁ (λ z → (z , (z , refl z))) refl (λ x' → total-path (refl _) (total-path (π₂ (π₂ x')) (trans-a≡x (π₂ (π₂ x')) (refl (π₁ x')))))

    comp-π₁-is-equiv : is-equiv (λ (f : (x : A) → free-path-space B) → λ (x : A) → π₁ (f x))
    comp-π₁-is-equiv = equiv-comp ((λ (y : free-path-space B) → π₁ y), π₁-is-equiv)

    d≡e : d ≡ e
    d≡e = equiv-is-inj (_ , comp-π₁-is-equiv) _ _ (refl f)

  funext : f ≡ g
  funext = map (λ f' x → π₁ (π₂ (f' x))) d≡e

open FunextNonDep public

-- Weak function extensionality (a product of contractible types is contractible)

module WeakFunext {i j : Level} {A : Set i} {P : A → Set j} (e : (x : A) → is-contr (P x)) where
  
  private
    P-is-unit : P ≡ (λ (x : A) → unit)
    P-is-unit = funext _ _(λ x → eq-to-path (contr-equiv-unit (e x)))

  weak-funext : is-contr ((x : A) → P x)
  weak-funext = transport (λ Q → is-contr ((x : A) → Q x)) (! P-is-unit) ((λ x → tt) , (λ y → funext _ _ (λ x → refl tt)))

open WeakFunext public

-- Naive dependent function extensionality
     
module FunextDep {i j : Level} {A : Set i} {P : A → Set j} (f g : (x : A) → P x) (h : (x : A) → f x ≡ g x) where
  
  private
    Q : A → Set j
    Q x = Σ (P x) (λ y → y ≡ f x)
  
    Q-contr : (x : A) → is-contr (Q x)
    Q-contr x = ((f x , refl (f x)) , pathto-contr)
  
    Q-sections-contr : is-contr ((x : A) → Q x)
    Q-sections-contr = weak-funext Q-contr
  
    Q-f : (x : A) → Q x
    Q-f x = (f x , refl _)
  
    Q-g : (x : A) → Q x
    Q-g x = (g x , ! (h x))
  
    Q-f≡Q-g : Q-f ≡ Q-g
    Q-f≡Q-g = is-contr-path _ Q-sections-contr Q-f Q-g

  abstract
    funext-dep : f ≡ g
    funext-dep = map (λ u x → π₁ (u x)) Q-f≡Q-g

open FunextDep public

-- Strong function extensionality is missing
