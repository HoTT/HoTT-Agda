{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pi
open import lib.types.TwoGroupoid
open import lib.types.PathSeq

module lib.groupoids.FunExtTwoGroupoid where

module _ {i j k} (A : Type i) (G : TwoOneSemiCategory j k) where

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

  fun-groupoid : TwoOneSemiCategory (lmax i j) (lmax i k)
  fun-groupoid =
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
