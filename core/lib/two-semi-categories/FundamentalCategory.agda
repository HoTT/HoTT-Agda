{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pi
open import lib.types.Truncation
open import lib.types.TwoSemiCategory
open import lib.two-semi-categories.Functor
open import lib.two-semi-categories.FunctorInverse
open import lib.two-semi-categories.GroupToCategory

module lib.two-semi-categories.FundamentalCategory where

module _ {i} (A : Type i) where

  2-type-fundamental-cat : {{_ : has-level 2 A}} → TwoSemiCategory i i
  2-type-fundamental-cat =
    record
    { El = A
    ; Arr = _==_
    ; Arr-level = λ _ _ → ⟨⟩
    ; two-semi-cat-struct = record
      { comp = _∙_
      ; assoc = λ a b c → ∙-assoc a b c
      ; pentagon-identity = λ p q r s → =ₛ-in (∙-assoc-pentagon p q r s)
      }
    }

  =ₜ-fundamental-cat : TwoSemiCategory i i
  =ₜ-fundamental-cat =
    record
    { El = Trunc 2 A
    ; Arr = _=ₜ_
    ; Arr-level = =ₜ-level
    ; two-semi-cat-struct = record
      { comp = λ {ta} p q → _∙ₜ_ {ta = ta} p q
      ; assoc = λ {ta} p q r → ∙ₜ-assoc {ta = ta} p q r
      ; pentagon-identity = λ {ta} p q r s → =ₛ-in (∙ₜ-assoc-pentagon {ta = ta} p q r s)
      }
    }

module _ {i} (A : Type i) where

  2-type-to-=ₜ-fundamental-cat
    : TwoSemiFunctor
        (2-type-fundamental-cat (Trunc 2 A))
        (=ₜ-fundamental-cat A)
  2-type-to-=ₜ-fundamental-cat =
    record
    { F₀ = idf (Trunc 2 A)
    ; F₁ = λ {ta} {tb} f → –> (=ₜ-equiv ta tb) f
    ; pres-comp = –>-=ₜ-equiv-pres-∙
      -- TODO: The following line takes a really long time to check
      -- Can we optimize this somehow?
    ; pres-comp-coh = λ {ta} p q r → =ₛ-in $ –>-=ₜ-equiv-pres-∙-coh {ta = ta} p q r
    }

  =ₜ-to-2-type-fundamental-cat
    : TwoSemiFunctor
        (=ₜ-fundamental-cat A)
        (2-type-fundamental-cat (Trunc 2 A))
  =ₜ-to-2-type-fundamental-cat =
    functor-inverse 2-type-to-=ₜ-fundamental-cat
      (idf-is-equiv (Trunc 2 A))
      (λ ta tb → snd (=ₜ-equiv ta tb))

  =ₜ-to-2-type-fundamental-cat-F₁ : ∀ {ta} {tb} (p : ta =ₜ tb)
    → TwoSemiFunctor.F₁ =ₜ-to-2-type-fundamental-cat p == <– (=ₜ-equiv ta tb) p
  =ₜ-to-2-type-fundamental-cat-F₁ p = idp

module _ {i} (C : Type i) (c₀ : C) {{C-level : has-level 1 C}} where

  open import lib.groups.LoopSpace

  fundamental-group-to-fundamental-groupoid
    : TwoSemiFunctor (group-to-cat (Ω^S-group 0 ⊙[ C , c₀ ]))
                                (2-type-fundamental-cat C {{raise-level 1 C-level}})
  fundamental-group-to-fundamental-groupoid =
    record
    { F₀ = λ _ → c₀
    ; F₁ = λ p → p
    ; pres-comp = λ p q → idp
    ; pres-comp-coh =
        λ p q r → =ₛ-in $
          prop-path (has-level-apply (has-level-apply C-level _ _) _ _) _ _
    }

module _ {i j} (A : Type i) (B : Type j) {{B-level : has-level 2 B}} where

  open import lib.two-semi-categories.FunCategory

  private

    app=-pres-comp : ∀ {f g h : A → B} (α : f == g) (β : g == h) → app= (α ∙ β) == (λ a → app= α a ∙ app= β a)
    app=-pres-comp α β = λ= (λ a → ap-∙ (λ f → f a) α β)

    abstract
      app=-pres-comp-coh : ∀ {f g h i : A → B} (α : f == g) (β : g == h) (γ : h == i)
        → app=-pres-comp (α ∙ β) γ ◃∙
          ap (λ s a → s a ∙ app= γ a) (app=-pres-comp α β) ◃∙
          λ= (λ a → ∙-assoc (app= α a) (app= β a) (app= γ a)) ◃∎
          =ₛ
          ap app= (∙-assoc α β γ) ◃∙
          app=-pres-comp α (β ∙ γ) ◃∙
          ap (λ s a → app= α a ∙ s a) (app=-pres-comp β γ) ◃∎
      app=-pres-comp-coh {f} idp idp γ =
        app=-pres-comp idp γ ◃∙
        ap (λ s a → s a ∙ app= γ a) (app=-pres-comp idp idp) ◃∙
        λ= (λ a → idp) ◃∎
          =ₛ⟨ 2 & 1 & =ₛ-in {t = _ ∎∎} (! (λ=-η idp)) ⟩
        app=-pres-comp idp γ ◃∙
        ap (λ s a → s a ∙ app= γ a) (app=-pres-comp idp idp) ◃∎
          =ₛ₁⟨ 1 & 1 & λ=-ap (λ a t → t ∙ app= γ a) (λ a → ap-∙ (λ f → f a) (idp {a = f}) idp) ⟩
        app=-pres-comp idp γ ◃∙
        app=-pres-comp idp γ ◃∎
          =ₛ₁⟨ 1 & 1 & ! (ap-idf (app=-pres-comp idp γ)) ⟩
        app=-pres-comp idp γ ◃∙
        ap (λ s a → s a) (app=-pres-comp idp γ) ◃∎
          =ₛ₁⟨ 0 & 0 & idp ⟩
        idp ◃∙
        app=-pres-comp idp γ ◃∙
        ap (λ s a → s a) (app=-pres-comp idp γ) ◃∎ ∎ₛ

  app=-functor : TwoSemiFunctor (2-type-fundamental-cat (A → B))
                                (fun-cat A (2-type-fundamental-cat B))
  app=-functor =
    record
    { F₀ = idf (A → B)
    ; F₁ = app=
    ; pres-comp = app=-pres-comp
    ; pres-comp-coh = app=-pres-comp-coh
    }

  λ=-functor : TwoSemiFunctor (fun-cat A (2-type-fundamental-cat B))
                              (2-type-fundamental-cat (A → B))
  λ=-functor =
    functor-inverse app=-functor
      (idf-is-equiv _)
      (λ f g → snd app=-equiv)

  λ=-functor-F₁ : ∀ {f g : A → B} (α : f ∼ g)
    → TwoSemiFunctor.F₁ λ=-functor α == λ= α
  λ=-functor-F₁ α = idp
