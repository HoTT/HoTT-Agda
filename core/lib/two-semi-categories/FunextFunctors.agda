{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.two-semi-categories.Functor
open import lib.two-semi-categories.FundamentalCategory
open import lib.two-semi-categories.FunctorInverse
open import lib.types.Pi using ()

module lib.two-semi-categories.FunextFunctors where

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
          =ₛ⟨ 2 & 1 & =ₛ-in {t = []} (! (λ=-η idp)) ⟩
        app=-pres-comp idp γ ◃∙
        ap (λ s a → s a ∙ app= γ a) (app=-pres-comp idp idp) ◃∎
          =ₛ₁⟨ 1 & 1 & λ=-ap (λ a t → t ∙ app= γ a) (λ a → ap-∙ (λ f → f a) (idp {a = f}) idp) ⟩
        app=-pres-comp idp γ ◃∙
        app=-pres-comp idp γ ◃∎
          =ₛ₁⟨ 1 & 1 & ! (ap-idf (app=-pres-comp idp γ)) ⟩
        app=-pres-comp idp γ ◃∙
        ap (λ s a → s a) (app=-pres-comp idp γ) ◃∎
          =ₛ⟨ 0 & 0 & contract ⟩
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

  private
    module app=-functor =
      TwoSemiFunctor app=-functor
    module app=-inverse =
      FunctorInverse
        app=-functor
        (idf-is-equiv _)
        (λ f g → snd app=-equiv)

  λ=-functor : TwoSemiFunctor (fun-cat A (2-type-fundamental-cat B))
                              (2-type-fundamental-cat (A → B))
  λ=-functor = app=-inverse.functor

  λ=-functor-pres-comp=λ=-∙ : ∀ {f g h : A → B} (α : f ∼ g) (β : g ∼ h)
    → app=-inverse.pres-comp α β == =ₛ-out (λ=-∙ α β)
  λ=-functor-pres-comp=λ=-∙ α β = =ₛ-out {t = =ₛ-out (λ=-∙ α β) ◃∎} $
    pres-comp α β ◃∎
      =ₛ⟨ pres-comp-β α β ⟩
    ap G₁' (G₁''-pres-comp α β) ◃∙
    G₁'-pres-comp (G₁'' α) (G₁'' β) ◃∎
      =ₛ⟨id⟩
    idp ◃∙
    G₁'-pres-comp α β ◃∎
      =ₛ⟨ 0 & 1 & expand [] ⟩
    G₁'-pres-comp α β ◃∎
      =ₛ⟨ G₁'-pres-comp-β α β ⟩
    ap2 (λ s t → G₁' (λ a → s a ∙ t a)) (F₁-η α) (F₁-η β) ◃∙
    ap G₁' (! (app=-functor.pres-comp (G₁' α) (G₁' β))) ◃∙
    G₁'-β (G₁' α ∙ G₁' β) ◃∎
      =ₛ⟨id⟩
    ap2 (λ s t → λ= (λ a → s a ∙ t a)) (! (λ= (app=-β α))) (! (λ= (app=-β β))) ◃∙
    ap λ= (! (λ= (λ a → ap-∙ (λ f → f a) (λ= α) (λ= β)))) ◃∙
    ! (λ=-η (λ= α ∙ λ= β)) ◃∎
      =ₛ₁⟨ 0 & 1 & step₈ ⟩
    ap λ= (! (λ= (λ a' → ap2 _∙_ (app=-β α a') (app=-β β a')))) ◃∙
    ap λ= (! (λ= (λ a' → ap-∙ (λ γ → γ a') (λ= α) (λ= β)))) ◃∙
    ! (λ=-η (λ= α ∙ λ= β)) ◃∎
      =ₛ⟨ 0 & 2 &
          ap-seq-=ₛ λ= $ ∙-!-seq $
          λ= (λ a' → ap-∙ (λ γ → γ a') (λ= α) (λ= β)) ◃∙
          λ= (λ a' → ap2 _∙_ (app=-β α a') (app=-β β a')) ◃∎ ⟩
    ap λ= (! (λ= (λ a' → ap-∙ (λ γ → γ a') (λ= α) (λ= β)) ∙
              λ= (λ a' → ap2 _∙_ (app=-β α a') (app=-β β a')))) ◃∙
    ! (λ=-η (λ= α ∙ λ= β)) ◃∎
      =ₛ₁⟨ 0 & 1 & ap-! λ= (λ= (λ a' → ap-∙ (λ γ → γ a') (λ= α) (λ= β)) ∙
                            λ= (λ a' → ap2 _∙_ (app=-β α a') (app=-β β a'))) ⟩
    ! (ap λ= (λ= (λ a' → ap-∙ (λ γ → γ a') (λ= α) (λ= β)) ∙
              λ= (λ a' → ap2 _∙_ (app=-β α a') (app=-β β a')))) ◃∙
    ! (λ=-η (λ= α ∙ λ= β)) ◃∎
      =ₛ₁⟨ 0 & 1 &
           ap (! ∘ ap λ=) $ =ₛ-out $
           ∙-λ= (λ a' → ap-∙ (λ γ → γ a') (λ= α) (λ= β))
                (λ a' → ap2 _∙_ (app=-β α a') (app=-β β a')) ⟩
    ! (ap λ= (λ= (λ a' → ap-∙ (λ γ → γ a') (λ= α) (λ= β) ∙
                         ap2 _∙_ (app=-β α a') (app=-β β a')))) ◃∙
    ! (λ=-η (λ= α ∙ λ= β)) ◃∎
      =ₛ⟨ =ₛ-in $
          ∙-! (ap λ= (λ= (λ a' → ap-∙ (λ γ → γ a') (λ= α) (λ= β) ∙
                                        ap2 _∙_ (app=-β α a') (app=-β β a'))))
              (λ=-η (λ= α ∙ λ= β)) ⟩
    ! (λ=-η (λ= α ∙ λ= β) ∙
       ap λ= (λ= (λ a' → ap-∙ (λ γ → γ a') (λ= α) (λ= β) ∙
                         ap2 _∙_ (app=-β α a') (app=-β β a')))) ◃∎ ∎ₛ
    where
    open app=-inverse
    step₈' : ap2 (λ s t a → s a ∙ t a) (λ= (app=-β α)) (λ= (app=-β β)) ==
             λ= (λ a' → ap2 _∙_ (app=-β α a') (app=-β β a'))
    step₈' =
      –>-is-inj app=-equiv _ _ $ λ= $ λ a →
      app= (ap2 (λ s t a' → s a' ∙ t a') (λ= (app=-β α)) (λ= (app=-β β))) a
        =⟨ ap-ap2 (λ f → f a) (λ s t a' → s a' ∙ t a') (λ= (app=-β α)) (λ= (app=-β β)) ⟩
      ap2 (λ s t → s a ∙ t a) (λ= (app=-β α)) (λ= (app=-β β))
        =⟨ ! (ap2-ap-lr _∙_ (λ f → f a) (λ f → f a) (λ= (app=-β α)) (λ= (app=-β β))) ⟩
      ap2 _∙_ (app= (λ= (app=-β α)) a) (app= (λ= (app=-β β)) a)
        =⟨ ap2 (ap2 _∙_) (app=-β (app=-β α) a) (app=-β (app=-β β) a) ⟩
      ap2 _∙_ (app=-β α a) (app=-β β a)
        =⟨ ! (app=-β (λ a' → ap2 _∙_ (app=-β α a') (app=-β β a')) a) ⟩
      app= (λ= (λ a' → ap2 _∙_ (app=-β α a') (app=-β β a'))) a =∎
    step₈ : ap2 (λ s t → λ= (λ a → s a ∙ t a)) (! (λ= (app=-β α))) (! (λ= (app=-β β))) ==
            ap λ= (! (λ= (λ a' → ap2 _∙_ (app=-β α a') (app=-β β a'))))
    step₈ =
      ap2 (λ s t → λ= (λ a → s a ∙ t a)) (! (λ= (app=-β α))) (! (λ= (app=-β β)))
        =⟨ ! (ap-ap2 λ= (λ s t a → s a ∙ t a) (! (λ= (app=-β α))) (! (λ= (app=-β β)))) ⟩
      ap λ= (ap2 (λ s t a → s a ∙ t a) (! (λ= (app=-β α))) (! (λ= (app=-β β))))
        =⟨ ap (ap λ=) (ap2-! (λ s t a → s a ∙ t a) (λ= (app=-β α)) (λ= (app=-β β))) ⟩
      ap λ= (! (ap2 (λ s t a → s a ∙ t a) (λ= (app=-β α)) (λ= (app=-β β))))
        =⟨ ap (ap λ= ∘ !) step₈' ⟩
      ap λ= (! (λ= (λ a' → ap2 _∙_ (app=-β α a') (app=-β β a')))) =∎
