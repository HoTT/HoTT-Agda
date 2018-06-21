{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pi
open import lib.types.TwoSemiCategory
open import lib.two-semi-categories.Functor

module lib.two-semi-categories.FunCategory where

module _ {i j k} (A : Type i) (G : TwoSemiCategory j k) where

  private
    module G = TwoSemiCategory G

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

  abstract
    fun-pentagon : {F G H I J : fun-El}
      (α : fun-Arr F G) (β : fun-Arr G H) (γ : fun-Arr H I) (δ : fun-Arr I J)
      → fun-assoc (fun-comp α β) γ δ ◃∙
        fun-assoc α β (fun-comp γ δ) ◃∎
        =ₛ
        ap (λ s → fun-comp s δ) (fun-assoc α β γ) ◃∙
        fun-assoc α (fun-comp β γ) δ ◃∙
        ap (fun-comp α) (fun-assoc β γ δ) ◃∎
    fun-pentagon α β γ δ =
      fun-assoc (fun-comp α β) γ δ ◃∙
      fun-assoc α β (fun-comp γ δ) ◃∎
        =ₛ⟨ ∙-λ= (λ a → G.assoc (G.comp (α a) (β a)) (γ a) (δ a))
                 (λ a → G.assoc (α a) (β a) (G.comp (γ a) (δ a))) ⟩
      λ= (λ a → G.assoc (G.comp (α a) (β a)) (γ a) (δ a) ∙
                G.assoc (α a) (β a) (G.comp (γ a) (δ a))) ◃∎
        =ₛ₁⟨ ap λ= (λ= (λ a → =ₛ-out (G.pentagon-identity (α a) (β a) (γ a) (δ a)))) ⟩
      λ= (λ a → ap (λ s → G.comp s (δ a)) (G.assoc (α a) (β a) (γ a)) ∙
                G.assoc (α a) (G.comp (β a) (γ a)) (δ a) ∙
                ap (G.comp (α a)) (G.assoc (β a) (γ a) (δ a))) ◃∎
        =ₛ⟨ λ=-∙ (λ a → ap (λ s → G.comp s (δ a)) (G.assoc (α a) (β a) (γ a)))
                 (λ a → G.assoc (α a) (G.comp (β a) (γ a)) (δ a) ∙
                        ap (G.comp (α a)) (G.assoc (β a) (γ a) (δ a))) ⟩
      λ= (λ a → ap (λ s → G.comp s (δ a)) (G.assoc (α a) (β a) (γ a)))◃∙
      λ= (λ a → G.assoc (α a) (G.comp (β a) (γ a)) (δ a) ∙
      ap (G.comp (α a)) (G.assoc (β a) (γ a) (δ a))) ◃∎
        =ₛ⟨ 1 & 1 & λ=-∙ (λ a → G.assoc (α a) (G.comp (β a) (γ a)) (δ a))
                         (λ a → ap (G.comp (α a)) (G.assoc (β a) (γ a) (δ a))) ⟩
      λ= (λ a → ap (λ s → G.comp s (δ a)) (G.assoc (α a) (β a) (γ a))) ◃∙
      fun-assoc α (fun-comp β γ) δ ◃∙
      λ= (λ a → ap (G.comp (α a)) (G.assoc (β a) (γ a) (δ a))) ◃∎
        =ₛ₁⟨ 0 & 1 & ! (λ=-ap (λ a s → G.comp s (δ a)) (λ a → G.assoc (α a) (β a) (γ a))) ⟩
      ap (λ s → fun-comp s δ) (fun-assoc α β γ) ◃∙
      fun-assoc α (fun-comp β γ) δ ◃∙
      λ= (λ a → ap (G.comp (α a)) (G.assoc (β a) (γ a) (δ a))) ◃∎
        =ₛ₁⟨ 2 & 1 & ! (λ=-ap (λ a → G.comp (α a)) (λ a → G.assoc (β a) (γ a) (δ a))) ⟩
      ap (λ s → fun-comp s δ) (fun-assoc α β γ) ◃∙
      fun-assoc α (fun-comp β γ) δ ◃∙
      ap (fun-comp α) (fun-assoc β γ δ) ◃∎ ∎ₛ

  fun-cat : TwoSemiCategory (lmax i j) (lmax i k)
  fun-cat =
    record
    { El = fun-El
    ; Arr = fun-Arr
    ; Arr-level = fun-Arr-level
    ; two-semi-cat-struct =
      record
      { comp = fun-comp
      ; assoc = fun-assoc
      ; pentagon-identity = fun-pentagon
      }
    }

module _ {i j₁ k₁ j₂ k₂} (A : Type i) {G : TwoSemiCategory j₁ k₁} {H : TwoSemiCategory j₂ k₂}
  (F : TwoSemiFunctor G H) where

  private
    module G = TwoSemiCategory G
    module H = TwoSemiCategory H
    module F = TwoSemiFunctor F
    module fun-G = TwoSemiCategory (fun-cat A G)
    module fun-H = TwoSemiCategory (fun-cat A H)

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
      → fun-pres-comp (fun-G.comp α β) γ ◃∙
        ap (λ s → fun-H.comp s (fun-F₁ γ)) (fun-pres-comp α β) ◃∙
        fun-H.assoc (fun-F₁ α) (fun-F₁ β) (fun-F₁ γ) ◃∎
        =ₛ
        ap fun-F₁ (fun-G.assoc α β γ) ◃∙
        fun-pres-comp α (fun-G.comp β γ) ◃∙
        ap (fun-H.comp (fun-F₁ α)) (fun-pres-comp β γ) ◃∎
    fun-pres-comp-coh α β γ =
      fun-pres-comp (fun-G.comp α β) γ ◃∙
      ap (λ s → fun-H.comp s (fun-F₁ γ)) (fun-pres-comp α β) ◃∙
      fun-H.assoc (fun-F₁ α) (fun-F₁ β) (fun-F₁ γ) ◃∎
        =ₛ₁⟨ 1 & 1 & λ=-ap (λ a s → H.comp s (fun-F₁ γ a) ) (λ a → F.pres-comp (α a) (β a)) ⟩
      fun-pres-comp (fun-G.comp α β) γ ◃∙
      λ= (λ a → ap (λ s → H.comp s (fun-F₁ γ a)) (F.pres-comp (α a) (β a))) ◃∙
      fun-H.assoc (fun-F₁ α) (fun-F₁ β) (fun-F₁ γ) ◃∎
        =ₛ⟨ ∙∙-λ= (λ a → F.pres-comp (G.comp (α a) (β a)) (γ a))
                  (λ a → ap (λ s → H.comp s (fun-F₁ γ a)) (F.pres-comp (α a) (β a)))
                  (λ a → H.assoc (fun-F₁ α a) (fun-F₁ β a) (fun-F₁ γ a)) ⟩
      λ= (λ a → F.pres-comp (G.comp (α a) (β a)) (γ a) ∙
                ap (λ s → H.comp s (fun-F₁ γ a)) (F.pres-comp (α a) (β a)) ∙
                H.assoc (fun-F₁ α a) (fun-F₁ β a) (fun-F₁ γ a)) ◃∎
        =ₛ₁⟨ ap λ= (λ= (λ a → =ₛ-out (F.pres-comp-coh (α a) (β a) (γ a)))) ⟩
      λ= (λ a → ap F.F₁ (G.assoc (α a) (β a) (γ a)) ∙
                F.pres-comp (α a) (G.comp (β a) (γ a)) ∙
                ap (H.comp (fun-F₁ α a)) (F.pres-comp (β a) (γ a))) ◃∎
        =ₛ⟨ λ=-∙∙ (λ a → ap F.F₁ (G.assoc (α a) (β a) (γ a)))
                  (λ a → F.pres-comp (α a) (G.comp (β a) (γ a)))
                  (λ a → ap (H.comp (fun-F₁ α a)) (F.pres-comp (β a) (γ a))) ⟩
      λ= (λ a → ap F.F₁ (G.assoc (α a) (β a) (γ a))) ◃∙
      fun-pres-comp α (fun-G.comp β γ) ◃∙
      λ= (λ a → ap (H.comp (fun-F₁ α a)) (F.pres-comp (β a) (γ a))) ◃∎
        =ₛ₁⟨ 0 & 1 & ! $ λ=-ap (λ _ → F.F₁) (λ a → G.assoc (α a) (β a) (γ a)) ⟩
      ap fun-F₁ (fun-G.assoc α β γ) ◃∙
      fun-pres-comp α (fun-G.comp β γ) ◃∙
      λ= (λ a → ap (H.comp (fun-F₁ α a)) (F.pres-comp (β a) (γ a))) ◃∎
        =ₛ₁⟨ 2 & 1 & ! $ λ=-ap (λ a → H.comp (fun-F₁ α a)) (λ a → F.pres-comp (β a) (γ a)) ⟩
      ap fun-F₁ (fun-G.assoc α β γ) ◃∙
      fun-pres-comp α (fun-G.comp β γ) ◃∙
      ap (fun-H.comp (fun-F₁ α)) (fun-pres-comp β γ) ◃∎ ∎ₛ

  fun-functor-map : TwoSemiFunctor (fun-cat A G) (fun-cat A H)
  fun-functor-map =
    record
    { F₀ = fun-F₀
    ; F₁ = fun-F₁
    ; pres-comp = fun-pres-comp
    ; pres-comp-coh = fun-pres-comp-coh
    }
