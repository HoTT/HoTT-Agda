{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.Equivalences
open import lib.Univalence
open import lib.NType
open import lib.PathGroupoid

module lib.Funext {i} {A : Type i} where

-- Naive non dependent function extensionality

module FunextNonDep {j} {B : Type j} {f g : A → B} (h : (x : A) → f x == g x)
  where

  private
    equiv-comp : {B C : Type j} (e : B ≃ C)
      → is-equiv (λ (g : A → B) → (λ x → –> e (g x)))
    equiv-comp {B} {C} e =
      equiv-induction {A = B} {B = C}
                      (λ {B} e → is-equiv (λ (g : A → B) → (λ x → –> e (g x))))
                      (λ A' → idf-is-equiv (A → A')) e

    free-path-space-B : Type j
    free-path-space-B = Σ B (λ x → Σ B (λ y → x == y))

    d : A → free-path-space-B
    d x = (f x , (f x , idp))

    e : A → free-path-space-B
    e x = (f x , (g x , h x))

    abstract
      fst-is-equiv : is-equiv (λ (y : free-path-space-B) → fst y)
      fst-is-equiv =
        is-eq fst (λ z → (z , (z , idp))) (λ _ → idp)
          (λ x' → ap (λ x → (_ , x))
                        (contr-has-all-paths (pathfrom-is-contr (fst x')) _ _))

      comp-fst-is-equiv : is-equiv (λ (f : A → free-path-space-B)
                                     → (λ x → fst (f x)))
      comp-fst-is-equiv = equiv-comp ((λ (y : free-path-space-B) → fst y),
                                     fst-is-equiv)

      d==e : d == e
      d==e = equiv-inj (_ , comp-fst-is-equiv) idp

  funext-nondep : f == g
  funext-nondep = ap (λ f' x → fst (snd (f' x))) d==e

open FunextNonDep

-- Weak function extensionality (a product of contractible types is
-- contractible)
module WeakFunext {j} {P : A → Type j} (e : (x : A) → is-contr (P x)) where

  P-is-unit : P == (λ x → Lift ⊤)
  P-is-unit = funext-nondep (λ x → ua (contr-equiv-Unit (e x)))

  abstract
    weak-funext : is-contr (Π A P)
    weak-funext = transport (λ Q → is-contr (Π A Q)) (! P-is-unit)
                            ((λ x → lift tt) , (λ y → funext-nondep (λ x → idp)))

open WeakFunext

-- Naive dependent function extensionality

module FunextDep {j} {P : A → Type j} {f g : Π A P} (h : (x : A) → f x == g x)
  where

  Q : A → Type j
  Q x = Σ (P x) (λ y → y == f x)

  abstract
    Q-is-contr : (x : A) → is-contr (Q x)
    Q-is-contr x = pathto-is-contr (f x)

    ΠAQ-is-contr : is-contr (Π A Q)
    ΠAQ-is-contr = weak-funext Q-is-contr

  Q-f : Π A Q
  Q-f x = (f x , idp)

  Q-g : Π A Q
  Q-g x = (g x , ! (h x))

  abstract
    Q-f==Q-g : Q-f == Q-g
    Q-f==Q-g = contr-has-all-paths ΠAQ-is-contr Q-f Q-g

  funext-p : f == g
  funext-p = ap (λ u x → fst (u x)) Q-f==Q-g

open FunextDep

happly : ∀ {j} {P : A → Type j} {f g : Π A P} (p : f == g) → ((x : A) → f x == g x)
happly p x = ap (λ u → u x) p

-- Strong function extensionality

module StrongFunextDep {j} {P : A → Type j} where

  funext-idp : (f : Π A P)
    → funext-p (λ x → idp {a = f x}) == idp
  funext-idp f = ap (ap (λ u x → fst (u x)))
    (contr-has-all-paths (=-preserves-level _
                         (ΠAQ-is-contr (λ x → idp)))
                         (Q-f==Q-g (λ x → idp)) idp)

  funext-happly-p : {f g : Π A P} (p : f == g)
    → funext-p (happly p) == p
  funext-happly-p {f} idp = funext-idp f

  happly-path : {f : Π A P} {u v : (x : A) → Q (λ x → idp {a = f x}) x}
    (p : u == v) (x : A)
    → happly (ap (λ u x → fst (u x)) p) x == snd (u x) ∙ ! (snd (v x))
  happly-path {u = u} idp x = ! (!-inv-r (snd (u x)))

  happly-funext-p : {f g : Π A P} (h : (x : A) → f x == g x)
    → happly (funext-p h) == h
  happly-funext-p h = funext-p (λ x → happly-path (Q-f==Q-g h) x
                                            ∙ !-! (h x))

  happly-is-equiv : {f g : Π A P} → is-equiv (happly {f = f} {g = g})
  happly-is-equiv = is-eq _ funext-p happly-funext-p funext-happly-p

  funext-is-equiv-p : {f g : Π A P}
    → is-equiv (funext-p {f = f} {g = g})
  funext-is-equiv-p = is-eq _ happly funext-happly-p happly-funext-p

open StrongFunextDep

-- We only export the following

module _ {j} {P : A → Type j} {f g : Π A P} where

  abstract
    funext : (h : (x : A) → f x == g x) → f == g
    funext = FunextDep.funext-p

    funext-happly : (p : f == g) → funext (happly p) == p
    funext-happly p = funext-happly-p p

    happly-funext : (h : (x : A) → f x == g x)
      → happly (funext h) == h
    happly-funext h = happly-funext-p h

    funext-is-equiv : is-equiv funext
    funext-is-equiv = StrongFunextDep.funext-is-equiv-p

  funext-equiv : ((x : A) → f x == g x) ≃ (f == g)
  funext-equiv = (funext , funext-is-equiv)

  happly-equiv : (f == g) ≃ ((x : A) → f x == g x)
  happly-equiv = (happly , happly-is-equiv)

  λ= = funext
  app= = happly
  app=-β = happly ∘ happly-funext
  λ=-η = funext-happly
