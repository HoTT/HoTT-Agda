{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pi
open import lib.types.TwoGroupoid
open import lib.groupoids.TwoOneSemiCatFunctorInverse
open import lib.types.PathSeq

module lib.groupoids.FunExtTwoGroupoid where

module _ {i j k} (A : Type i) (G : TwoOneSemiCategory j k) where

  private
    module G = TwoOneSemiCategory G

  fun-El : Type (lmax i j)
  fun-El = A → G.El

  fun-Arr : fun-El → fun-El → Type (lmax i k)
  fun-Arr F G = ∀ a → G.Arr (F a) (G a)

  fun-Arr-level : (F G : fun-El) → has-level 1 (fun-Arr F G)
  fun-Arr-level F G = Π-level (λ a → G.Arr-level (F a) (G a))

  fun-comp : {F G H : fun-El} (α : fun-Arr F G) (β : fun-Arr G H)
    → fun-Arr F H
  fun-comp α β a = G.comp (α a) (β a)

  fun-assoc : {F G H I : fun-El} (α : fun-Arr F G) (β : fun-Arr G H) (γ : fun-Arr H I)
    → fun-comp (fun-comp α β) γ == fun-comp α (fun-comp β γ)
  fun-assoc α β γ = λ= (λ a → G.assoc (α a) (β a) (γ a))

  fun-pentagon : {F G H I J : fun-El}
    (α : fun-Arr F G) (β : fun-Arr G H) (γ : fun-Arr H I) (δ : fun-Arr I J)
    →  fun-assoc (fun-comp α β) γ δ ∙ fun-assoc α β (fun-comp γ δ)
    == ap (λ s → fun-comp s δ) (fun-assoc α β γ) ∙
       fun-assoc α (fun-comp β γ) δ ∙ ap (fun-comp α) (fun-assoc β γ δ)
  fun-pentagon α β γ δ =
    fun-assoc (fun-comp α β) γ δ ∙ fun-assoc α β (fun-comp γ δ)
      =⟨ ∙-λ= (λ a → G.assoc (G.comp (α a) (β a)) (γ a) (δ a))
              (λ a → G.assoc (α a) (β a) (G.comp (γ a) (δ a))) ⟩
    λ= (λ a → G.assoc (G.comp (α a) (β a)) (γ a) (δ a) ∙ G.assoc (α a) (β a) (G.comp (γ a) (δ a)))
      =⟨ ap λ= (λ= (λ a → G.pentagon-identity (α a) (β a) (γ a) (δ a))) ⟩
    λ= (λ a → ap (λ s → G.comp s (δ a)) (G.assoc (α a) (β a) (γ a)) ∙
              G.assoc (α a) (G.comp (β a) (γ a)) (δ a) ∙
              ap (G.comp (α a)) (G.assoc (β a) (γ a) (δ a)))
      =⟨ ! (∙-λ= (λ a → ap (λ s → G.comp s (δ a)) (G.assoc (α a) (β a) (γ a)))
                 (λ a → G.assoc (α a) (G.comp (β a) (γ a)) (δ a) ∙
                        ap (G.comp (α a)) (G.assoc (β a) (γ a) (δ a)))) ⟩
    (λ= (λ a → ap (λ s → G.comp s (δ a)) (G.assoc (α a) (β a) (γ a)))◃∙
     λ= (λ a → G.assoc (α a) (G.comp (β a) (γ a)) (δ a) ∙
               ap (G.comp (α a)) (G.assoc (β a) (γ a) (δ a))) ◃∎)
      =↯=⟨ 1 & 1 & (fun-assoc α (fun-comp β γ) δ ◃∙
                    λ= (λ a → ap (G.comp (α a)) (G.assoc (β a) (γ a) (δ a))) ◃∎)
             & ! (∙-λ= (λ a → G.assoc (α a) (G.comp (β a) (γ a)) (δ a))
                       (λ a → ap (G.comp (α a)) (G.assoc (β a) (γ a) (δ a)))) ⟩
    (λ= (λ a → ap (λ s → G.comp s (δ a)) (G.assoc (α a) (β a) (γ a))) ◃∙
     fun-assoc α (fun-comp β γ) δ ◃∙
     λ= (λ a → ap (G.comp (α a)) (G.assoc (β a) (γ a) (δ a))) ◃∎)
      =↯=⟨ 0 & 1 & ap (λ s → fun-comp s δ) (fun-assoc α β γ) ◃∎
           & ! (λ=-ap (λ a s → G.comp s (δ a)) (λ a → G.assoc (α a) (β a) (γ a))) ⟩
    (ap (λ s → fun-comp s δ) (fun-assoc α β γ) ◃∙
     fun-assoc α (fun-comp β γ) δ ◃∙
     λ= (λ a → ap (G.comp (α a)) (G.assoc (β a) (γ a) (δ a))) ◃∎)
      =↯=⟨ 2 & 1 & ap (fun-comp α) (fun-assoc β γ δ) ◃∎
             & ! (λ=-ap (λ a → G.comp (α a)) (λ a → G.assoc (β a) (γ a) (δ a))) ⟩
    (ap (λ s → fun-comp s δ) (fun-assoc α β γ) ◃∙
     fun-assoc α (fun-comp β γ) δ ◃∙
     ap (fun-comp α) (fun-assoc β γ δ) ◃∎) ↯∎

  fun-semi-cat : TwoOneSemiCategory (lmax i j) (lmax i k)
  fun-semi-cat =
    record
    { El = fun-El
    ; Arr = fun-Arr
    ; Arr-level = fun-Arr-level
    ; two-one-semi-cat-struct =
      record
      { comp = fun-comp
      ; assoc = fun-assoc
      ; pentagon-identity = fun-pentagon
      }
    }

module _ {i j₁ k₁ j₂ k₂} (A : Type i) (G : TwoOneSemiCategory j₁ k₁) (H : TwoOneSemiCategory j₂ k₂)
  (F : TwoOneSemiCategoryFunctor G H) where

  module G = TwoOneSemiCategory G
  module H = TwoOneSemiCategory H
  module F = TwoOneSemiCategoryFunctor F
  module fun-G = TwoOneSemiCategory (fun-semi-cat A G)
  module fun-H = TwoOneSemiCategory (fun-semi-cat A H)

  fun-F₀ : fun-G.El → fun-H.El
  fun-F₀ I = λ a → F.F₀ (I a)

  fun-F₁ : {I J : fun-G.El} → fun-G.Arr I J → fun-H.Arr (fun-F₀ I) (fun-F₀ J)
  fun-F₁ α = λ a → F.F₁ (α a)

  fun-pres-comp : {I J K : fun-G.El} (α : fun-G.Arr I J) (β : fun-G.Arr J K)
    → fun-F₁ (fun-G.comp α β) == fun-H.comp (fun-F₁ α) (fun-F₁ β)
  fun-pres-comp α β = λ= (λ a → F.pres-comp (α a) (β a))

  abstract
    fun-pres-comp-coh : {I J K L : fun-G.El}
      (α : fun-G.Arr I J) (β : fun-G.Arr J K) (γ : fun-G.Arr K L)
      → fun-pres-comp (fun-G.comp α β) γ ∙
        ap (λ s → fun-H.comp s (fun-F₁ γ)) (fun-pres-comp α β) ∙
        fun-H.assoc (fun-F₁ α) (fun-F₁ β) (fun-F₁ γ)
        ==
        ap fun-F₁ (fun-G.assoc α β γ) ∙
        fun-pres-comp α (fun-G.comp β γ) ∙
        ap (fun-H.comp (fun-F₁ α)) (fun-pres-comp β γ)
    fun-pres-comp-coh α β γ =
      (fun-pres-comp (fun-G.comp α β) γ ◃∙
      ap (λ s → fun-H.comp s (fun-F₁ γ)) (fun-pres-comp α β) ◃∙
      fun-H.assoc (fun-F₁ α) (fun-F₁ β) (fun-F₁ γ) ◃∎)
        =↯=⟨ 1 & 1 & λ= (λ a → ap (λ s → H.comp s (fun-F₁ γ a)) (F.pres-comp (α a) (β a))) ◃∎
              & λ=-ap (λ a s → H.comp s (fun-F₁ γ a) ) (λ a → F.pres-comp (α a) (β a)) ⟩
      (fun-pres-comp (fun-G.comp α β) γ ◃∙
      λ= (λ a → ap (λ s → H.comp s (fun-F₁ γ a)) (F.pres-comp (α a) (β a))) ◃∙
      fun-H.assoc (fun-F₁ α) (fun-F₁ β) (fun-F₁ γ) ◃∎)
        =↯=⟨ 1 & 2 & λ= (λ a → ap (λ s → H.comp s (fun-F₁ γ a)) (F.pres-comp (α a) (β a)) ∙
                                H.assoc (fun-F₁ α a) (fun-F₁ β a) (fun-F₁ γ a)) ◃∎
                & ∙-λ= (λ a → ap (λ s → H.comp s (fun-F₁ γ a)) (F.pres-comp (α a) (β a)))
                      (λ a → H.assoc (fun-F₁ α a) (fun-F₁ β a) (fun-F₁ γ a)) ⟩
      (fun-pres-comp (fun-G.comp α β) γ ◃∙
      λ= (λ a → ap (λ s → H.comp s (fun-F₁ γ a)) (F.pres-comp (α a) (β a)) ∙
                H.assoc (fun-F₁ α a) (fun-F₁ β a) (fun-F₁ γ a)) ◃∎)
        ↯=⟨ ∙-λ= (λ a → F.pres-comp (G.comp (α a) (β a)) (γ a))
                (λ a → ap (λ s → H.comp s (fun-F₁ γ a)) (F.pres-comp (α a) (β a)) ∙
                        H.assoc (fun-F₁ α a) (fun-F₁ β a) (fun-F₁ γ a)) ⟩
      λ= (λ a → F.pres-comp (G.comp (α a) (β a)) (γ a) ∙
                ap (λ s → H.comp s (fun-F₁ γ a)) (F.pres-comp (α a) (β a)) ∙
                H.assoc (fun-F₁ α a) (fun-F₁ β a) (fun-F₁ γ a))
        =⟨ ap λ= (λ= (λ a → F.pres-comp-coh (α a) (β a) (γ a))) ⟩
      λ= (λ a → ap F.F₁ (G.assoc (α a) (β a) (γ a)) ∙
                F.pres-comp (α a) (G.comp (β a) (γ a)) ∙
                ap (H.comp (fun-F₁ α a)) (F.pres-comp (β a) (γ a)))
        =⟨ ! (∙-λ= (λ a → ap F.F₁ (G.assoc (α a) (β a) (γ a)))
                  (λ a → F.pres-comp (α a) (G.comp (β a) (γ a)) ∙
                          ap (H.comp (fun-F₁ α a)) (F.pres-comp (β a) (γ a)))) ⟩
      (λ= (λ a → ap F.F₁ (G.assoc (α a) (β a) (γ a))) ◃∙
      λ= (λ a → F.pres-comp (α a) (G.comp (β a) (γ a)) ∙
                ap (H.comp (fun-F₁ α a)) (F.pres-comp (β a) (γ a))) ◃∎)
        =↯=⟨ 1 & 1 & (fun-pres-comp α (fun-G.comp β γ) ◃∙
                      λ= (λ a → ap (H.comp (fun-F₁ α a)) (F.pres-comp (β a) (γ a))) ◃∎)
                      & ! $ ∙-λ= (λ a → F.pres-comp (α a) (G.comp (β a) (γ a)))
                                (λ a → ap (H.comp (fun-F₁ α a)) (F.pres-comp (β a) (γ a))) ⟩
      (λ= (λ a → ap F.F₁ (G.assoc (α a) (β a) (γ a))) ◃∙
      fun-pres-comp α (fun-G.comp β γ) ◃∙
      λ= (λ a → ap (H.comp (fun-F₁ α a)) (F.pres-comp (β a) (γ a))) ◃∎)
        =↯=⟨ 0 & 1 & ap fun-F₁ (fun-G.assoc α β γ) ◃∎
              & ! $ λ=-ap (λ _ → F.F₁) (λ a → G.assoc (α a) (β a) (γ a)) ⟩
      (ap fun-F₁ (fun-G.assoc α β γ) ◃∙
      fun-pres-comp α (fun-G.comp β γ) ◃∙
      λ= (λ a → ap (H.comp (fun-F₁ α a)) (F.pres-comp (β a) (γ a))) ◃∎)
        =↯=⟨ 2 & 1 & ap (fun-H.comp (fun-F₁ α)) (fun-pres-comp β γ) ◃∎
              & ! $ λ=-ap (λ a → H.comp (fun-F₁ α a)) (λ a → F.pres-comp (β a) (γ a)) ⟩
      (ap fun-F₁ (fun-G.assoc α β γ) ◃∙
      fun-pres-comp α (fun-G.comp β γ) ◃∙
      ap (fun-H.comp (fun-F₁ α)) (fun-pres-comp β γ) ◃∎) ↯∎

  fun-functor : TwoOneSemiCategoryFunctor (fun-semi-cat A G) (fun-semi-cat A H)
  fun-functor =
    record
    { F₀ = fun-F₀
    ; F₁ = fun-F₁
    ; pres-comp = fun-pres-comp
    ; pres-comp-coh = fun-pres-comp-coh
    }

module _ {i j} (A : Type i) (B : Type j) {{B-level : has-level 2 B}} where

  open import lib.groupoids.FundamentalPreTwoGroupoid

  private

    A→B-semi-cat : TwoOneSemiCategory (lmax i j) (lmax i j)
    A→B-semi-cat = fundamental-two-one-semi-category-of-a-two-type (A → B)

    Bᴬ-functor-semi-cat : TwoOneSemiCategory (lmax i j) (lmax i j)
    Bᴬ-functor-semi-cat = fun-semi-cat A (fundamental-two-one-semi-category-of-a-two-type B)

    fun-ext-pres-comp : ∀ {f g h : A → B} (α : f == g) (β : g == h) → app= (α ∙ β) == (λ a → app= α a ∙ app= β a)
    fun-ext-pres-comp α β = λ= (λ a → ap-∙ (λ f → f a) α β)

    fun-ext-pres-comp-coh : ∀ {f g h i : A → B} (α : f == g) (β : g == h) (γ : h == i)
      → fun-ext-pres-comp (α ∙ β) γ ∙
        ap (λ s a → s a ∙ app= γ a) (fun-ext-pres-comp α β) ∙
        λ= (λ a → ∙-assoc (app= α a) (app= β a) (app= γ a))
        ==
        ap app= (∙-assoc α β γ) ∙
        fun-ext-pres-comp α (β ∙ γ) ∙
        ap (λ s a → app= α a ∙ s a) (fun-ext-pres-comp β γ)
    fun-ext-pres-comp-coh {f} idp idp γ =
      (fun-ext-pres-comp idp γ ◃∙
       ap (λ s a → s a ∙ app= γ a) (fun-ext-pres-comp idp idp) ◃∙
       λ= (λ a → idp) ◃∎)
        =↯=⟨ 2 & 1 & (_ ∎∎)
               & ! (λ=-η idp) ⟩
      (fun-ext-pres-comp idp γ ◃∙
       ap (λ s a → s a ∙ app= γ a) (fun-ext-pres-comp idp idp) ◃∎)
        ↯=⟨ idp ⟩
      (fun-ext-pres-comp idp γ ◃∙
       ap (λ s a → s a ∙ app= γ a) (λ= (λ a → ap-∙ (λ f → f a) (idp {a = f}) idp)) ◃∎)
        =↯=⟨ 1 & 1 & fun-ext-pres-comp idp γ ◃∎
               & λ=-ap (λ a t → t ∙ app= γ a) (λ a → ap-∙ (λ f → f a) (idp {a = f}) idp) ⟩
      (fun-ext-pres-comp idp γ ◃∙
       fun-ext-pres-comp idp γ ◃∎)
        =↯=⟨ 1 & 1 & ap (λ s a → s a) (fun-ext-pres-comp idp γ) ◃∎
               & ! (ap-idf (fun-ext-pres-comp idp γ)) ⟩
      (fun-ext-pres-comp idp γ ◃∙
       ap (λ s a → s a) (fun-ext-pres-comp idp γ) ◃∎) ↯∎

  fun-ext-functor : TwoOneSemiCategoryFunctor A→B-semi-cat Bᴬ-functor-semi-cat
  fun-ext-functor =
    record
    { F₀ = idf (A → B)
    ; F₁ = app=
    ; pres-comp = fun-ext-pres-comp
    ; pres-comp-coh = fun-ext-pres-comp-coh
    }

  fun-ext-functor-inv : TwoOneSemiCategoryFunctor Bᴬ-functor-semi-cat A→B-semi-cat
  fun-ext-functor-inv =
    semi-cat-functor-inverse fun-ext-functor
      (idf-is-equiv _)
      (λ f g → snd app=-equiv)
