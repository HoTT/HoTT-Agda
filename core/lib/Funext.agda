{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.Function
open import lib.Equivalence
open import lib.Univalence
open import lib.NType
open import lib.PathFunctor
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

module _ where

  app= : ∀ {j} {P : A → Type j} {f g : Π A P}
    → f == g → f ∼ g
  app= p x = ap (λ u → u x) p

  private
    module λ=-is-equiv {j} {P : A → Type j} {f g : Π A P}
      = is-equiv (StrongFunextDep.λ=-is-equiv {f = f} {g = g})

  abstract
    λ= : ∀ {j} {P : A → Type j} {f g : Π A P}
      → f ∼ g → f == g
    λ= = FunextDep.λ=

    app=-β : ∀ {j} {P : A → Type j} {f g : Π A P}
      → (p : f ∼ g) (x : A) → app= (λ= p) x == p x
    app=-β p x = app= (λ=-is-equiv.g-f p) x

    λ=-η : ∀ {j} {P : A → Type j} {f g : Π A P}
      → (p : f == g) → p == λ= (app= p)
    λ=-η p = ! (λ=-is-equiv.f-g p)

    λ=-app=-adj : ∀ {j} {P : A → Type j} {f g : Π A P}
      → (p : f ∼ g) → ap λ= (λ= (app=-β p)) == ! (λ=-η (λ= p))
    λ=-app=-adj p =
      ap λ= (λ= (app=-β p))
        =⟨ ap (ap λ=) (! (λ=-η (λ=-is-equiv.g-f p))) ⟩
      ap λ= (λ=-is-equiv.g-f p)
        =⟨ λ=-is-equiv.adj p ⟩
      λ=-is-equiv.f-g (λ= p)
        =⟨ ! (!-! (λ=-is-equiv.f-g (λ= p))) ⟩
      ! (λ=-η (λ= p)) =∎

    λ=-app=-adj' : ∀ {j} {P : A → Type j} {f g : Π A P}
      → (p : f == g) → ap app= (λ=-η p) == ! (λ= (app=-β (app= p)))
    λ=-app=-adj' p =
      ap app= (λ=-η p)
        =⟨ ap-! app= (λ=-is-equiv.f-g p) ⟩
      ! (ap app= (λ=-is-equiv.f-g p))
        =⟨ ap ! (λ=-is-equiv.adj' p) ⟩
      ! (λ=-is-equiv.g-f (app= p))
        =⟨ ap ! (λ=-η (λ=-is-equiv.g-f (app= p))) ⟩
      ! (λ= (app=-β (app= p))) =∎

  λ=-equiv : ∀ {j} {P : A → Type j} {f g : Π A P}
    → (f ∼ g) ≃ (f == g)
  λ=-equiv = (λ= , λ=-is-equiv) where
    abstract
      λ=-is-equiv : is-equiv λ=
      λ=-is-equiv = StrongFunextDep.λ=-is-equiv

  app=-equiv : ∀ {j} {P : A → Type j} {f g : Π A P}
    → (f == g) ≃ (f ∼ g)
  app=-equiv {f = f} {g = g} = (app= , app=-is-equiv)
    where
    app=-λ= : ∀ (h : f ∼ g) → app= (λ= h) == h
    app=-λ= h = λ= (app=-β h)
    λ=-app= : ∀ (h : f == g) → λ= (app= h) == h
    λ=-app= = ! ∘ λ=-η
    abstract
      adj : ∀ p → ap app= (λ=-app= p) == app=-λ= (app= p)
      adj p =
        ap app= (λ=-app= p)
          =⟨ ap-! app= (λ=-η p) ⟩
        ! (ap app= (λ=-η p))
          =⟨ ap ! (λ=-app=-adj' p) ⟩
        ! (! (app=-λ= (app= p)))
          =⟨ !-! (app=-λ= (app= p)) ⟩
        app=-λ= (app= p) =∎
    app=-is-equiv : is-equiv app=
    app=-is-equiv = -- is-eq _ λ= app=-λ= λ=-app=
      record
      { g = λ=
      ; f-g = app=-λ=
      ; g-f = λ=-app=
      ; adj = adj
      }

{- Functoriality of application and function extensionality -}

module _ {j} {B : A → Type j} {f g h : Π A B}
         (α : f ∼ g) (β : g ∼ h) where

  ∙-λ=-seq : λ= α ∙ λ= β =-= λ= (λ x → α x ∙ β x)
  ∙-λ=-seq =
    λ= α ∙ λ= β
      =⟪ λ=-η (λ= α ∙ λ= β) ⟫
    λ= (app= (λ= α ∙ λ= β))
      =⟪ ap λ= (λ= (λ a' → ap-∙ (λ γ → γ a') (λ= α) (λ= β) ∙
                           ap2 _∙_ (app=-β α a') (app=-β β a'))) ⟫
    λ= (λ a → α a ∙ β a) ∎∎

  ∙-λ= : λ= α ◃∙ λ= β ◃∎ =ₛ λ= (λ x → α x ∙ β x) ◃∎
  ∙-λ= = =ₛ-in (↯ ∙-λ=-seq)

  λ=-∙ : λ= (λ x → α x ∙ β x) ◃∎ =ₛ λ= α ◃∙ λ= β ◃∎
  λ=-∙ = !ₛ ∙-λ=

module _ {j} {B : A → Type j} {f g h : Π A B}
         (α : f ∼ g) (β : g ∼ h) (a : A) where
  app=-β-coh₁ : app= (λ= α ∙ λ= β) a =-= α a ∙ β a
  app=-β-coh₁ =
    app= (λ= α ∙ λ= β) a
      =⟪ ap-∙ (λ γ → γ a) (λ= α) (λ= β) ⟫
    app= (λ= α) a ∙ app= (λ= β) a
      =⟪ ap2 _∙_ (app=-β α a) (app=-β β a) ⟫
    α a ∙ β a ∎∎

  app=-β-coh₂ : app= (λ= α ∙ λ= β) a =-= α a ∙ β a
  app=-β-coh₂ =
    app= (λ= α ∙ λ= β) a
      =⟪ ap (λ p → app= p a) (=ₛ-out (∙-λ= α β)) ⟫
    app= (λ= (λ a' → α a' ∙ β a')) a
      =⟪ app=-β (λ a' → α a' ∙ β a') a ⟫
    α a ∙ β a ∎∎

  app=-β-coh : app=-β-coh₁ =ₛ app=-β-coh₂
  app=-β-coh =
    ap-∙ (λ γ → γ a) (λ= α) (λ= β) ◃∙
    ap2 _∙_ (app=-β α a) (app=-β β a) ◃∎
      =ₛ₁⟨ idp ⟩
    (ap-∙ (λ γ → γ a) (λ= α) (λ= β) ∙
     ap2 _∙_ (app=-β α a) (app=-β β a)) ◃∎
      =ₛ₁⟨ ! $ app=-β (λ a' → ap-∙ (λ γ → γ a') (λ= α) (λ= β) ∙
                              ap2 _∙_ (app=-β α a') (app=-β β a'))
                       a ⟩
    app= (λ= (λ a → ap-∙ (λ f → f a) (λ= α) (λ= β) ∙
                    ap2 _∙_ (app=-β α a) (app=-β β a))) a ◃∎
      =ₛ⟨ pre-rotate-in $ !ₛ $
          homotopy-naturality (λ γ → app= (λ= γ) a)
                              (λ γ → γ a)
                              (λ γ → app=-β γ a)
                              (λ= (λ a' → ap-∙ (λ γ → γ a') (λ= α) (λ= β) ∙
                                          ap2 _∙_ (app=-β α a') (app=-β β a')))
        ⟩
    ! (app=-β (λ a' → app= (λ= α ∙ λ= β) a') a) ◃∙
    ap (λ γ → app= (λ= γ) a)
       (λ= (λ a' → ap-∙ (λ γ → γ a') (λ= α) (λ= β) ∙
                   ap2 _∙_ (app=-β α a') (app=-β β a'))) ◃∙
    app=-β (λ a' → α a' ∙ β a') a ◃∎
      =ₛ₁⟨ 0 & 1 & step₄ ⟩
    ap (λ p → app= p a) (λ=-η (λ= α ∙ λ= β)) ◃∙
    ap (λ γ → app= (λ= γ) a)
       (λ= (λ a' → ap-∙ (λ γ → γ a') (λ= α) (λ= β) ∙
                   ap2 _∙_ (app=-β α a') (app=-β β a'))) ◃∙
    app=-β (λ a' → α a' ∙ β a') a ◃∎
      =ₛ₁⟨ 1 & 1 &
           ap-∘ (λ p → app= p a) λ=
                (λ= (λ a' → ap-∙ (λ γ → γ a') (λ= α) (λ= β) ∙
                            ap2 _∙_ (app=-β α a') (app=-β β a'))) ⟩
    ap (λ p → app= p a) (λ=-η (λ= α ∙ λ= β)) ◃∙
    ap (λ p → app= p a)
       (ap λ=
           (λ= (λ a' → ap-∙ (λ γ → γ a') (λ= α) (λ= β) ∙
                       ap2 _∙_ (app=-β α a') (app=-β β a')))) ◃∙
    app=-β (λ a' → α a' ∙ β a') a ◃∎
      =ₛ⟨ 0 & 2 & ∙-ap-seq (λ p → app= p a) (∙-λ=-seq α β) ⟩
    ap (λ p → app= p a) (=ₛ-out (∙-λ= α β)) ◃∙
    app=-β (λ a' → α a' ∙ β a') a ◃∎ ∎ₛ
    where
    step₄ : ! (app=-β (λ a' → app= (λ= α ∙ λ= β) a') a) ==
            ap (λ p → app= p a) (λ=-η (λ= α ∙ λ= β))
    step₄ =
      ! (app=-β (λ a' → app= (λ= α ∙ λ= β) a') a)
        =⟨ ap ! (! (app=-β (app=-β (λ a' → app= (λ= α ∙ λ= β) a')) a)) ⟩
      ! (app= (λ= (app=-β (λ a' → app= (λ= α ∙ λ= β) a'))) a)
        =⟨ !-ap (λ γ → γ a) (λ= (app=-β (λ a' → app= (λ= α ∙ λ= β) a'))) ⟩
      app= (! (λ= (app=-β (λ a' → app= (λ= α ∙ λ= β) a')))) a
        =⟨ ap (λ p → app= p a) (! (λ=-app=-adj' (λ= α ∙ λ= β))) ⟩
      app= (ap app= (λ=-η (λ= α ∙ λ= β))) a
        =⟨ ∘-ap (λ f → f a) app= (λ=-η (λ= α ∙ λ= β)) ⟩
      ap (λ p → app= p a) (λ=-η (λ= α ∙ λ= β)) =∎

module _ {j} {B : A → Type j} {f g h k : Π A B}
         (α : f ∼ g) (β : g ∼ h) (γ : h ∼ k) where

  ∙∙-λ= : λ= α ◃∙ λ= β ◃∙ λ= γ ◃∎ =ₛ λ= (λ x → α x ∙ β x ∙ γ x) ◃∎
  ∙∙-λ= =
    λ= α ◃∙ λ= β ◃∙ λ= γ ◃∎
      =ₛ⟨ 1 & 2 & ∙-λ= β γ ⟩
    λ= α ◃∙ λ= (λ x → β x ∙ γ x) ◃∎
      =ₛ⟨ ∙-λ= α (λ x → β x ∙ γ x) ⟩
    λ= (λ x → α x ∙ β x ∙ γ x) ◃∎ ∎ₛ

  λ=-∙∙ : λ= (λ x → α x ∙ β x ∙ γ x) ◃∎ =ₛ λ= α ◃∙ λ= β ◃∙ λ= γ ◃∎
  λ=-∙∙ = !ₛ ∙∙-λ=

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

  λ=-! : (α : f ∼ g) → ! (λ= α) == λ= (! ∘ α)
  λ=-! α = ! (!-λ= α)

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
