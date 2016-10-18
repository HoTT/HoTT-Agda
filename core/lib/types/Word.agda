{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Empty
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Group
open import lib.types.Nat
open import lib.types.List

module lib.types.Word {i} where

module _ (A : Type i) where

  PlusMinus : Type i
  PlusMinus = Coprod A A

  Word : Type i
  Word = List PlusMinus

module _ {A : Type i} where

  flip : PlusMinus A → PlusMinus A
  flip (inl a) = inr a
  flip (inr a) = inl a

  flip-flip : ∀ x → flip (flip x) == x
  flip-flip (inl x) = idp
  flip-flip (inr x) = idp

  Word-flip : Word A → Word A
  Word-flip = map flip

  Word-flip-flip : ∀ w → Word-flip (Word-flip w) == w
  Word-flip-flip nil = idp
  Word-flip-flip (x :: l) = ap2 _::_ (flip-flip x) (Word-flip-flip l)

module _ {A : Type i} {j} (G : Group j) where
  private
    module G = Group G

  PlusMinus-extendᴳ : (A → G.El) → (PlusMinus A → G.El)
  PlusMinus-extendᴳ f (inl a) = f a
  PlusMinus-extendᴳ f (inr a) = G.inv (f a)

  Word-extendᴳ : (A → G.El) → (Word A → G.El)
  Word-extendᴳ f = foldr G.comp G.ident ∘ map (PlusMinus-extendᴳ f)

  abstract
    Word-extendᴳ-++ : ∀ f l₁ l₂
      → Word-extendᴳ f (l₁ ++ l₂) == G.comp (Word-extendᴳ f l₁) (Word-extendᴳ f l₂)
    Word-extendᴳ-++ f nil l₂ = ! $ G.unit-l _
    Word-extendᴳ-++ f (x :: l₁) l₂ =
        ap (G.comp (PlusMinus-extendᴳ f x)) (Word-extendᴳ-++ f l₁ l₂)
      ∙ ! (G.assoc (PlusMinus-extendᴳ f x) (Word-extendᴳ f l₁)  (Word-extendᴳ f l₂))
