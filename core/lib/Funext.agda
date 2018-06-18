{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.Function
open import lib.Equivalence
open import lib.Univalence
open import lib.NType
open import lib.PathGroupoid
open import lib.PathSeq

{-
A proof of function extensionality from the univalence axiom.
-}

module lib.Funext {i} {A : Type i} where

-- Naive non dependent function extensionality

module FunextNonDep {j} {B : Type j} {f g : A → B} (h : f ∼ g)
  where

  private
    equiv-comp : {B C : Type j} (e : B ≃ C)
      → is-equiv (λ (g : A → B) → (λ x → –> e (g x)))
    equiv-comp {B} e =
      equiv-induction (λ {B} e → is-equiv (λ (g : A → B) → (λ x → –> e (g x))))
                      (λ A' → snd (ide (A → A'))) e

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
                        (contr-has-all-paths _ _))

      comp-fst-is-equiv : is-equiv (λ (f : A → free-path-space-B)
                                     → (λ x → fst (f x)))
      comp-fst-is-equiv = equiv-comp ((λ (y : free-path-space-B) → fst y),
                                     fst-is-equiv)

      d==e : d == e
      d==e = equiv-is-inj comp-fst-is-equiv _ _ idp

  λ=-nondep : f == g
  λ=-nondep = ap (λ f' x → fst (snd (f' x))) d==e

open FunextNonDep using (λ=-nondep)

-- Weak function extensionality (a product of contractible types is
-- contractible)
module WeakFunext {j} {P : A → Type j} (e : (x : A) → is-contr (P x)) where

  P-is-Unit : P == (λ x → Lift Unit)
  P-is-Unit = λ=-nondep (λ x → ua (contr-equiv-LiftUnit (e x)))

  abstract
    weak-λ= : is-contr (Π A P)
    weak-λ= = transport (λ Q → is-contr (Π A Q)) (! P-is-Unit)
                            (has-level-in ((λ x → lift unit) , (λ y → λ=-nondep (λ x → idp))))

-- Naive dependent function extensionality

module FunextDep {j} {P : A → Type j} {f g : Π A P} (h : f ∼ g)
  where

  open WeakFunext

  Q : A → Type j
  Q x = Σ (P x) (λ y → f x == y)

  abstract
    Q-is-contr : (x : A) → is-contr (Q x)
    Q-is-contr x = pathfrom-is-contr (f x)

    instance
      ΠAQ-is-contr : is-contr (Π A Q)
      ΠAQ-is-contr = weak-λ= Q-is-contr

  Q-f : Π A Q
  Q-f x = (f x , idp)

  Q-g : Π A Q
  Q-g x = (g x , h x)

  abstract
    Q-f==Q-g : Q-f == Q-g
    Q-f==Q-g = contr-has-all-paths Q-f Q-g

  λ= : f == g
  λ= = ap (λ u x → fst (u x)) Q-f==Q-g

-- Strong function extensionality

module StrongFunextDep {j} {P : A → Type j} where

  open FunextDep

  app= : ∀ {f g : Π A P} (p : f == g) → f ∼ g
  app= p x = ap (λ u → u x) p

  λ=-idp : (f : Π A P)
    → idp == λ= (λ x → idp {a = f x})
  λ=-idp f = ap (ap (λ u x → fst (u x)))
    (contr-has-all-paths {{=-preserves-level
                           (ΠAQ-is-contr (λ x → idp))}}
                         idp (Q-f==Q-g (λ x → idp)))

  λ=-η : {f g : Π A P} (p : f == g)
    → p == λ= (app= p)
  λ=-η {f} idp = λ=-idp f

  app=-β : {f g : Π A P} (h : f ∼ g) (x : A)
    → app= (λ= h) x == h x
  app=-β h = app=-path (Q-f==Q-g h)  where

    app=-path : {f : Π A P} {u v : (x : A) → Q (λ x → idp {a = f x}) x}
      (p : u == v) (x : A)
      → app= (ap (λ u x → fst (u x)) p) x == ! (snd (u x)) ∙ snd (v x)
    app=-path {u = u} idp x = ! (!-inv-l (snd (u x)))

  app=-is-equiv : {f g : Π A P} → is-equiv (app= {f = f} {g = g})
  app=-is-equiv = is-eq _ λ= (λ h → λ= (app=-β h)) (! ∘ λ=-η)

  λ=-is-equiv : {f g : Π A P}
    → is-equiv (λ= {f = f} {g = g})
  λ=-is-equiv = is-eq _ app= (! ∘ λ=-η) (λ h → λ= (app=-β h))

-- We only export the following

module _ {j} {P : A → Type j} {f g : Π A P} where

  app= : f == g → f ∼ g
  app= p x = ap (λ u → u x) p

  abstract
    λ= : f ∼ g → f == g
    λ= = FunextDep.λ=

    app=-β : (p : f ∼ g) (x : A) → app= (λ= p) x == p x
    app=-β = StrongFunextDep.app=-β

    λ=-η : (p : f == g) → p == λ= (app= p)
    λ=-η = StrongFunextDep.λ=-η

  λ=-equiv : (f ∼ g) ≃ (f == g)
  λ=-equiv = (λ= , λ=-is-equiv) where
    abstract
      λ=-is-equiv : is-equiv λ=
      λ=-is-equiv = StrongFunextDep.λ=-is-equiv

  app=-equiv : (f == g) ≃ (f ∼ g)
  app=-equiv = (app= , app=-is-equiv) where
    abstract
      app=-λ= : ∀ (h : f ∼ g) → app= (λ= h) == h
      app=-λ= h = FunextDep.λ= (app=-β h)
      λ=-app= : ∀ (h : f == g) → λ= (app= h) == h
      λ=-app= = ! ∘ λ=-η
    app=-is-equiv : is-equiv app=
    app=-is-equiv = is-eq _ λ= app=-λ= λ=-app=

{- Functoriality of application and function extensionality -}

module _ {j} {B : A → Type j} {f g h : Π A B} where

  ∙-app= : (α : f == g) (β : g == h)
    → α ◃∙ β ◃∎ =ₛ λ= (λ x → app= α x ∙ app= β x) ◃∎
  ∙-app= idp β = =ₛ-in (λ=-η β)

  ∙-λ= : (α : f ∼ g) (β : g ∼ h)
    → λ= α ◃∙ λ= β ◃∎ =ₛ λ= (λ x → α x ∙ β x) ◃∎
  ∙-λ= α β = =ₛ-in $
    =ₛ-out (∙-app= (λ= α) (λ= β)) ∙
    ap λ= (λ= (λ x → ap (λ w → w ∙ app= (λ= β) x) (app=-β α x) ∙
                     ap (λ w → α x ∙ w) (app=-β β x)))

∙∙-λ= : ∀ {j} {B : A → Type j} {f g h k : Π A B}
  (α : f ∼ g) (β : g ∼ h) (γ : h ∼ k)
  → λ= α ◃∙ λ= β ◃∙ λ= γ ◃∎ =ₛ λ= (λ x → α x ∙ β x ∙ γ x) ◃∎
∙∙-λ= α β γ =
  λ= α ◃∙ λ= β ◃∙ λ= γ ◃∎
    =ₛ⟨ 1 & 2 & ∙-λ= β γ ⟩
  λ= α ◃∙ λ= (λ x → β x ∙ γ x) ◃∎
    =ₛ⟨ ∙-λ= α (λ x → β x ∙ γ x) ⟩
  λ= (λ x → α x ∙ β x ∙ γ x) ◃∎ ∎ₛ

module _ {j} {B : A → Type j} {f g : Π A B} where

  !-app= : (α : f == g) → λ= (! ∘ app= α) == ! α
  !-app= idp = ! (λ=-η idp)

  !-λ= : (α : f ∼ g) → λ= (! ∘ α) == ! (λ= α)
  !-λ= α =
    λ= (! ∘ α)
      =⟨ ap λ= (λ= (λ a → ap ! (! (app=-β α a)))) ⟩
    λ= (! ∘ app= (λ= α))
      =⟨ !-app= (λ= α) ⟩
    ! (λ= α) =∎

module _ {j k} {B : A → Type j} {C : A → Type k}
  {f g : Π A B} (h : (a : A) → B a → C a) where

  app=-ap : (α : f == g)
    → ap (λ f' a → h a (f' a)) α == λ= (λ a → ap (h a) (app= α a))
  app=-ap idp = λ=-η idp

  λ=-ap : (α : f ∼ g)
    → ap (λ f' a → h a (f' a)) (λ= α) == λ= (λ a → ap (h a) (α a))
  λ=-ap α =
    ap (λ f' a → h a (f' a)) (λ= α)
      =⟨ app=-ap (λ= α) ⟩
    λ= (λ a → ap (h a) (app= (λ= α) a))
      =⟨ ap λ= (λ= (λ a → ap (ap (h a)) (app=-β α a))) ⟩
    λ= (λ a → ap (h a) (α a)) =∎
