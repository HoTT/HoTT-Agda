{-# OPTIONS --without-K #-}

open import Types
open import Paths
open import Contractible
open import Equivalences
open import Univalence

module Funext where

-- Naive non dependent function extensionality

module FunextNonDep {i j} {A : Set i} {B : Set j} {f g : A → B} (h : (x : A) → f x ≡ g x) where

  private
    equiv-comp : ∀ {i j} {A : Set i} {B C : Set j} (f : B ≃ C)
      → is-equiv (λ (g : A → B) → λ (x : A) → f $ (g x))
    equiv-comp {A = A} f = equiv-induction (λ B C f → is-equiv (λ (g : A → B) → λ (x : A) → f $ (g x))) (λ A' y → id-is-equiv (A → A') y) _ _ f

    free-path-space-B : Set _
    free-path-space-B = Σ B (λ x → Σ B (λ y → x ≡ y))

    d : A → free-path-space-B
    d x = (f x , (f x , refl (f x)))

    e : A → free-path-space-B
    e x = (f x , (g x , h x))

    abstract
      π₁-is-equiv : is-equiv (λ (y : free-path-space-B) → π₁ y)
      π₁-is-equiv =
        iso-is-eq π₁ (λ z → (z , (z , refl z))) refl (λ x' → total-path (refl _) (total-path (π₂ (π₂ x')) (trans-a≡x (π₂ (π₂ x')) (refl (π₁ x')))))

      comp-π₁-is-equiv : is-equiv (λ (f : (x : A) → free-path-space-B) → λ (x : A) → π₁ (f x))
      comp-π₁-is-equiv = equiv-comp ((λ (y : free-path-space-B) → π₁ y), π₁-is-equiv)

      d≡e : d ≡ e
      d≡e = equiv-is-inj (_ , comp-π₁-is-equiv) _ _ (refl f)

  funext : f ≡ g
  funext = map (λ f' x → π₁ (π₂ (f' x))) d≡e

open FunextNonDep public

-- Weak function extensionality (a product of contractible types is contractible)

module WeakFunext {i j} {A : Set i} {P : A → Set j} (e : (x : A) → is-contr (P x)) where
  
  private
    P-is-unit : P ≡ (λ (x : A) → unit)
    P-is-unit = funext (λ x → eq-to-path (contr-equiv-unit (e x)))

  abstract
    weak-funext : is-contr ((x : A) → P x)
    weak-funext = transport (λ Q → is-contr ((x : A) → Q x)) (! P-is-unit) ((λ x → tt) , (λ y → funext (λ x → refl tt)))

open WeakFunext public

-- Naive dependent function extensionality
     
module FunextDep {i j} {A : Set i} {P : A → Set j} {f g : (x : A) → P x} (h : (x : A) → f x ≡ g x) where
  
  Q : A → Set j
  Q x = Σ (P x) (λ y → y ≡ f x)

  abstract
    Q-contr : (x : A) → is-contr (Q x)
    Q-contr x = ((f x , refl (f x)) , pathto-is-contr)
    
    Q-sections-contr : is-contr ((x : A) → Q x)
    Q-sections-contr = weak-funext Q-contr
    
  Q-f : (x : A) → Q x
  Q-f x = (f x , refl _)
    
  Q-g : (x : A) → Q x
  Q-g x = (g x , ! (h x))
  
  abstract
    Q-f≡Q-g : Q-f ≡ Q-g
    Q-f≡Q-g = is-contr-path _ Q-sections-contr Q-f Q-g

  funext-dep : f ≡ g
  funext-dep = map (λ u x → π₁ (u x)) Q-f≡Q-g
  
open FunextDep public

-- Strong function extensionality

happly : ∀ {i j} {A : Set i} {P : A → Set j} {f g : (x : A) → P x} (p : f ≡ g) → ((x : A) → f x ≡ g x)
happly p x = map (λ u → u x) p

module StrongFunextDep {i j} {A : Set i} {P : A → Set j} where

  funext-dep-refl : (f : (x : A) → P x) → funext-dep (λ x → refl (f x)) ≡ refl f
  funext-dep-refl f = map (map (λ u x → π₁ (u x)))
    (is-contr-path (Q-f r ≡ Q-g r) (path-contr-contr _ (Q-sections-contr r) (Q-f r) (Q-g r)) (Q-f≡Q-g r) (refl _)) where
    r : (x : A) → f x ≡ f x
    r = λ x → refl (f x)

  funext-dep-happly : {f g : (x : A) → P x} (p : f ≡ g) → funext-dep (happly p) ≡ p
  funext-dep-happly (refl f) = funext-dep-refl f

  happly-path : {f : (x : A) → P x} {u v : (x : A) → Q (λ x → refl (f x)) x} (p : u ≡ v) (x : A)
    → happly (map (λ u x → π₁ (u x)) p) x ≡ π₂ (u x) ∘ ! (π₂ (v x))
  happly-path (refl u) x = ! (opposite-right-inverse (π₂ (u x)))

  happly-funext-dep : {f g : (x : A) → P x} (h : (x : A) → f x ≡ g x) → happly (funext-dep h) ≡ h
  happly-funext-dep h = funext-dep (λ x → happly-path (Q-f≡Q-g h) x ∘ opposite-opposite (h x))

  abstract
    happly-is-equiv : {f g : (x : A) → P x} → is-equiv (happly {f = f} {g = g})
    happly-is-equiv = iso-is-eq _ funext-dep happly-funext-dep funext-dep-happly
  
  abstract
    funext-dep-is-equiv : {f g : (x : A) → P x} → is-equiv (funext-dep {f = f} {g = g})
    funext-dep-is-equiv = iso-is-eq _ happly funext-dep-happly happly-funext-dep

open StrongFunextDep public

