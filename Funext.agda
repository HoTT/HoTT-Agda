{-# OPTIONS --without-K #-}

open import Types
open import Paths
open import HLevel
open import Equivalences
open import Univalence

module Funext {i} {A : Set i} where

-- Naive non dependent function extensionality

module FunextNonDep {j} {B : Set j} {f g : A → B} (h : (x : A) → f x ≡ g x)
  where

  private
    equiv-comp : {B C : Set j} (f : B ≃ C)
      → is-equiv (λ (g : A → B) → (λ x → f ☆ (g x)))
    equiv-comp f =
      equiv-induction (λ {B} f → is-equiv (λ (g : A → B) → (λ x → f ☆ (g x))))
                      (λ A' y → id-is-equiv (A → A') y) f

    free-path-space-B : Set j
    free-path-space-B = Σ B (λ x → Σ B (λ y → x ≡ y))

    d : A → free-path-space-B
    d x = (f x , (f x , refl (f x)))

    e : A → free-path-space-B
    e x = (f x , (g x , h x))

    abstract
      π₁-is-equiv : is-equiv (λ (y : free-path-space-B) → π₁ y)
      π₁-is-equiv =
        iso-is-eq π₁ (λ z → (z , (z , refl z))) refl
          (λ x' → Σ-eq (refl _)
                    (Σ-eq (π₂ (π₂ x'))
                      (trans-cst≡id (π₂ (π₂ x')) (refl (π₁ x')))))

      comp-π₁-is-equiv : is-equiv (λ (f : A → free-path-space-B)
                                     → (λ x → π₁ (f x)))
      comp-π₁-is-equiv = equiv-comp ((λ (y : free-path-space-B) → π₁ y),
                                     π₁-is-equiv)

      d≡e : d ≡ e
      d≡e = equiv-is-inj (_ , comp-π₁-is-equiv) _ _ (refl f)

  funext-nondep : f ≡ g
  funext-nondep = map (λ f' x → π₁ (π₂ (f' x))) d≡e

open FunextNonDep

-- Weak function extensionality (a product of contractible types is
-- contractible)
module WeakFunext {j} {P : A → Set j} (e : (x : A) → is-contr (P x)) where

  P-is-unit : P ≡ (λ x → unit)
  P-is-unit = funext-nondep (λ x → eq-to-path (contr-equiv-unit (e x)))

  abstract
    weak-funext : is-contr (Π A P)
    weak-funext = transport (λ Q → is-contr (Π A Q)) (! P-is-unit)
                            ((λ x → tt) , (λ y → funext-nondep (λ x → refl tt)))

open WeakFunext

-- Naive dependent function extensionality

module FunextDep {j} {P : A → Set j} {f g : Π A P} (h : (x : A) → f x ≡ g x)
  where

  Q : A → Set j
  Q x = Σ (P x) (λ y → y ≡ f x)

  abstract
    Q-is-contr : (x : A) → is-contr (Q x)
    Q-is-contr x = pathto-is-contr (f x)

    ΠAQ-is-contr : is-contr (Π A Q)
    ΠAQ-is-contr = weak-funext Q-is-contr

  Q-f : Π A Q
  Q-f x = (f x , refl _)

  Q-g : Π A Q
  Q-g x = (g x , ! (h x))

  abstract
    Q-f≡Q-g : Q-f ≡ Q-g
    Q-f≡Q-g = contr-has-all-paths ΠAQ-is-contr Q-f Q-g

  funext-p : f ≡ g
  funext-p = map (λ u x → π₁ (u x)) Q-f≡Q-g

open FunextDep

happly : ∀ {j} {P : A → Set j} {f g : Π A P} (p : f ≡ g) → ((x : A) → f x ≡ g x)
happly p x = map (λ u → u x) p

-- Strong function extensionality

module StrongFunextDep {j} {P : A → Set j} where

  funext-refl : (f : Π A P)
    → funext-p (λ x → refl (f x)) ≡ refl f
  funext-refl f = map (map (λ u x → π₁ (u x)))
    (contr-has-all-paths (≡-is-truncated _
                         (ΠAQ-is-contr (λ x → refl _)))
                         (Q-f≡Q-g (λ x → refl _)) (refl _))

  funext-happly-p : {f g : Π A P} (p : f ≡ g)
    → funext-p (happly p) ≡ p
  funext-happly-p (refl f) = funext-refl f

  happly-path : {f : Π A P} {u v : (x : A) → Q (λ x → refl (f x)) x}
    (p : u ≡ v) (x : A)
    → happly (map (λ u x → π₁ (u x)) p) x ≡ π₂ (u x) ∘ ! (π₂ (v x))
  happly-path (refl u) x = ! (opposite-right-inverse (π₂ (u x)))

  happly-funext-p : {f g : Π A P} (h : (x : A) → f x ≡ g x)
    → happly (funext-p h) ≡ h
  happly-funext-p h = funext-p (λ x → happly-path (Q-f≡Q-g h) x
                                            ∘ opposite-opposite (h x))

  happly-is-equiv : {f g : Π A P} → is-equiv (happly {f = f} {g = g})
  happly-is-equiv = iso-is-eq _ funext-p happly-funext-p funext-happly-p

  funext-is-equiv-p : {f g : Π A P}
    → is-equiv (funext-p {f = f} {g = g})
  funext-is-equiv-p = iso-is-eq _ happly funext-happly-p happly-funext-p

open StrongFunextDep

-- We only export the following

module _ {j} {P : A → Set j} {f g : Π A P} where

  abstract
    funext : (h : (x : A) → f x ≡ g x) → f ≡ g
    funext = FunextDep.funext-p

    funext-happly : (p : f ≡ g) → funext (happly p) ≡ p
    funext-happly p = funext-happly-p p

    happly-funext : (h : (x : A) → f x ≡ g x)
      → happly (funext h) ≡ h
    happly-funext h = happly-funext-p h

    funext-is-equiv : is-equiv funext
    funext-is-equiv = StrongFunextDep.funext-is-equiv-p

  funext-equiv : ((x : A) → f x ≡ g x) ≃ (f ≡ g)
  funext-equiv = (funext , funext-is-equiv)

  happly-equiv : (f ≡ g) ≃ ((x : A) → f x ≡ g x)
  happly-equiv = (happly , happly-is-equiv)
