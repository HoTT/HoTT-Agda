{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Empty
open import lib.types.Group
open import lib.types.Int
open import lib.types.List
open import lib.types.Nat
open import lib.types.Pi
open import lib.types.Sigma

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

  Word-inverse : Word A → Word A
  Word-inverse = reverse ∘ Word-flip

  Word-inverse-inverse : ∀ w → Word-inverse (Word-inverse w) == w
  Word-inverse-inverse w =
    Word-inverse (Word-inverse w)
      =⟨ reverse-map flip (Word-inverse w) ⟩
    Word-flip (reverse (reverse (Word-flip w)))
      =⟨ ap Word-flip (reverse-reverse (Word-flip w)) ⟩
    Word-flip (Word-flip w)
      =⟨ Word-flip-flip w ⟩
    w =∎

  Word-exp : A → ℤ → Word A
  Word-exp a (pos 0) = nil
  Word-exp a (pos (S n)) = inl a :: Word-exp a (pos n)
  Word-exp a (negsucc 0) = inr a :: nil
  Word-exp a (negsucc (S n)) = inr a :: Word-exp a (negsucc n)

module _ {A : Type i} {j} (G : Group j) where
  private
    module G = Group G

  module _ (f : A → G.El) where
    PlusMinus-extendᴳ : PlusMinus A → G.El
    PlusMinus-extendᴳ (inl a) = f a
    PlusMinus-extendᴳ (inr a) = G.inv (f a)

    PlusMinus-extendᴳ-flip : ∀ x → PlusMinus-extendᴳ (flip x) == G.inv (PlusMinus-extendᴳ x)
    PlusMinus-extendᴳ-flip (inl a) = idp
    PlusMinus-extendᴳ-flip (inr a) = ! (G.inv-inv (f a))

    Word-extendᴳ : Word A → G.El
    Word-extendᴳ = foldr G.comp G.ident ∘ map PlusMinus-extendᴳ

  abstract
    Word-extendᴳ-++ : ∀ f l₁ l₂
      → Word-extendᴳ f (l₁ ++ l₂) == G.comp (Word-extendᴳ f l₁) (Word-extendᴳ f l₂)
    Word-extendᴳ-++ f nil l₂ = ! $ G.unit-l _
    Word-extendᴳ-++ f (x :: l₁) l₂ =
        ap (G.comp (PlusMinus-extendᴳ f x)) (Word-extendᴳ-++ f l₁ l₂)
      ∙ ! (G.assoc (PlusMinus-extendᴳ f x) (Word-extendᴳ f l₁)  (Word-extendᴳ f l₂))

module _ {A : Type i} {j} (G : AbGroup j) where
  private
    module G = AbGroup G

  abstract
    PlusMinus-extendᴳ-comp : ∀ (f g : A → G.El) x
      → PlusMinus-extendᴳ G.grp (λ a → G.comp (f a) (g a)) x
      == G.comp (PlusMinus-extendᴳ G.grp f x) (PlusMinus-extendᴳ G.grp g x)
    PlusMinus-extendᴳ-comp f g (inl a) = idp
    PlusMinus-extendᴳ-comp f g (inr a) = G.inv-comp (f a) (g a) ∙ G.comm (G.inv (g a)) (G.inv (f a))

    Word-extendᴳ-comp : ∀ (f g : A → G.El) l
      → Word-extendᴳ G.grp (λ a → G.comp (f a) (g a)) l
      == G.comp (Word-extendᴳ G.grp f l) (Word-extendᴳ G.grp g l)
    Word-extendᴳ-comp f g nil = ! (G.unit-l G.ident)
    Word-extendᴳ-comp f g (x :: l) =
        ap2 G.comp (PlusMinus-extendᴳ-comp f g x) (Word-extendᴳ-comp f g l)
      ∙ G.interchange (PlusMinus-extendᴳ G.grp f x) (PlusMinus-extendᴳ G.grp g x)
          (Word-extendᴳ G.grp f l) (Word-extendᴳ G.grp g l)
