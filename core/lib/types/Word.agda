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

  -- The following six functions prove things like if [x ∷ v ≡ y ∷ w],
  -- then [x ≡ y].
  -- This is not as easy as it sounds, you cannot directly induct on the equality
  -- (because [x ∷ v] is not a general element of type word), so you have to
  -- extract the head, but it’s not always possible…

  {-
  Word= : (v w : Word) → Type i
  Word= nil         nil         = Lift ⊤
  Word= nil         (y    :: w) = Lift ⊥
  Word= nil         (y inv:: w) = Lift ⊥
  Word= (x    :: v) nil         = Lift ⊥
  Word= (x    :: v) (y    :: w) = (x == y) × (v == w)
  Word= (x    :: v) (y inv:: w) = Lift ⊥
  Word= (x inv:: v) nil         = Lift ⊥
  Word= (x inv:: v) (y    :: w) = Lift ⊥
  Word= (x inv:: v) (y inv:: w) = (x == y) × (v == w)

  Word=-out : {v w : Word} (p : v == w) → Word= v w
  Word=-out {v = nil}       idp = lift unit
  Word=-out {v = x    :: v} idp = (idp , idp)
  Word=-out {v = x inv:: v} idp = (idp , idp)

  Word=-in : {v w : Word} → Word= v w → v == w
  Word=-in {nil}       {nil}       _         = idp
  Word=-in {nil}       {y    :: w} (lift ())
  Word=-in {nil}       {y inv:: w} (lift ())
  Word=-in {x    :: v} {nil}       (lift ())
  Word=-in {x    :: v} {y    :: w} (p , q)   = ap2 _::_ p q
  Word=-in {x    :: v} {y inv:: w} (lift ())
  Word=-in {x inv:: v} {nil}       (lift ())
  Word=-in {x inv:: v} {y    :: w} (lift ())
  Word=-in {x inv:: v} {y inv:: w} (p , q)   = ap2 _inv::_ p q

  Word-fst= : {x y : A} {v w : Word} (p : x :: v == y :: w) → x == y
  Word-fst= p = fst (Word=-out p)

  Word-snd= : {x y : A} {v w : Word} (p : x :: v == y :: w) → v == w
  Word-snd= p = snd (Word=-out p)

  Word-fst=' : {x y : A} {v w : Word} (p : x inv:: v == y inv:: w) → x == y
  Word-fst=' p = fst (Word=-out p)

  Word-snd=' : {x y : A} {v w : Word} (p : x inv:: v == y inv:: w) → v == w
  Word-snd=' p = snd (Word=-out p)
  -}
