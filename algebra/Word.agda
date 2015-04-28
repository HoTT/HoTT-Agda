{-# OPTIONS --without-K #-}

open import HoTT hiding (_::_)

module algebra.Word {i} (A : Type i) where

  data Word : Type i where
    nil : Word
    _::_ : A → Word → Word
    _inv::_ : A → Word → Word
  infixr 60 _::_ _inv::_

  -- The following six functions prove things like if [x ∷ v ≡ y ∷ w],
  -- then [x ≡ y].
  -- This is not as easy as it sounds, you cannot directly induct on the equality
  -- (because [x ∷ v] is not a general element of type word), so you have to
  -- extract the head, but it’s not always possible…

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

