{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Nat
open import lib.types.Sigma

module lib.types.PathSeq where

{-
This is a library on reified equational reasoning.
When you write the following (with the usual equational reasoning combinators):

  t : a == e
  t = a =⟨ p ⟩
      b =⟨ q ⟩
      c =⟨ r ⟩
      d =⟨ s ⟩
      e ∎

it just creates the concatenation of [p], [q], [r] and [s] and there is no way
to say “remove the last step to get the path from [a] to [d]”.
With the present library you would write:

  t : PathSeq a e
  t = a =⟪ p ⟫
      b =⟪ q ⟫
      c =⟪ r ⟫
      d =⟪ s ⟫
      e ∎∎

Then the actual path from [a] to [e] is [↯ t], and you can strip any number
of steps from the beginning or the end:

  ↯ t !2
-}

infix  2 _∎∎
infixr 2 _=⟪_⟫_

data PathSeq {i} {A : Type i} : A → A → Type i where
  _∎∎ : (a : A) → PathSeq a a
  _=⟪_⟫_ : (a : A) {a' a'' : A} (p : a == a') (s : PathSeq a' a'') → PathSeq a a''

infix 4 _=-=_
_=-=_ = PathSeq

infixr 2 _=⟪idp⟫_

_=⟪idp⟫_ : ∀ {i} {A : Type i} (a : A) {a' : A} (s : PathSeq a a') → PathSeq a a'
a =⟪idp⟫ s = s

module _ {i} {A : Type i} where

  infix 1 ↯_

  ↯_ : {a a' : A} (s : PathSeq a a') → a == a'
  ↯ a ∎∎ = idp
  ↯ a =⟪ p ⟫ a' ∎∎ = p
  ↯ a =⟪ p ⟫ s = p ∙ (↯ s)

  private
    point-from-start : (n : ℕ) {a a' : A} (s : PathSeq a a') → A
    point-from-start O {a} s = a
    point-from-start (S n) (a ∎∎) = a
    point-from-start (S n) (a =⟪ p ⟫ s) = point-from-start n s

  _-! : (n : ℕ) {a a' : A} (s : PathSeq a a') → PathSeq (point-from-start n s) a'
  (O -!) s = s
  (S n -!) (a ∎∎) = a ∎∎
  (S n -!) (a =⟪ p ⟫ s) = (n -!) s

  private
    last1 : {a a' : A} (s : PathSeq a a') → A
    last1 (a ∎∎) = a
    last1 (a =⟪ p ⟫ a' ∎∎) = a
    last1 (a =⟪ p ⟫ s) = last1 s

    strip : {a a' : A} (s : PathSeq a a') → PathSeq a (last1 s)
    strip (a ∎∎) = a ∎∎
    strip (a =⟪ p ⟫ a' ∎∎) = a ∎∎
    strip (a =⟪ p ⟫ a' =⟪ p' ⟫ s) = a =⟪ p ⟫ strip (a' =⟪ p' ⟫ s)

    point-from-end : (n : ℕ) {a a' : A} (s : PathSeq a a') → A
    point-from-end O {a} {a'} s = a'
    point-from-end (S n) s = point-from-end n (strip s)

  !- : (n : ℕ) {a a' : A} (s : PathSeq a a') → PathSeq a (point-from-end n s)
  !- O s = s
  !- (S n) s = !- n (strip s)

  _-# : (n : ℕ) {a a' : A} (s : PathSeq a a') → PathSeq a (point-from-start n s)
  (O -#) s = _ ∎∎
  (S n -#) (a ∎∎) = a ∎∎
  (S n -#) (a =⟪ p ⟫ s) = a =⟪ p ⟫ (n -#) s

  private
    split : {a a' : A} (s : PathSeq a a')
      → Σ A (λ a'' → (PathSeq a a'') × (a'' == a'))
    split (a ∎∎) = (a , ((a ∎∎) , idp))
    split (a =⟪ p ⟫ a' ∎∎) = (a , ((a ∎∎) , p))
    split (a =⟪ p ⟫ s) = let (a'' , (t , q)) = split s in (a'' , ((a =⟪ p ⟫ t) , q))

    _∙∙_ : {a a' a'' : A} (s : PathSeq a a') (p : a' == a'') → PathSeq a a''
    (a ∎∎) ∙∙ p = a =⟪ p ⟫ _ ∎∎
    (a =⟪ p ⟫ s) ∙∙ p' = a =⟪ p ⟫ s ∙∙ p'

    point-from-end' : (n : ℕ) {a a' : A} (s : PathSeq a a') → A
    point-from-end' n (a ∎∎) = a
    point-from-end' O (a =⟪ p ⟫ s) = point-from-end' O s
    point-from-end' (S n) (a =⟪ p ⟫ s) = point-from-end' n (fst (snd (split (a =⟪ p ⟫ s))))

  #- : (n : ℕ) {a a' : A} (s : PathSeq a a') → PathSeq (point-from-end' n s) a'
  #- n (a ∎∎) = a ∎∎
  #- O (a =⟪ p ⟫ s) = #- O s
  #- (S n) (a =⟪ p ⟫ s) = let (a' , (t , q)) = split (a =⟪ p ⟫ s) in #- n t ∙∙ q

  _!0 = !- 0
  _!1 = !- 1
  _!2 = !- 2
  _!3 = !- 3
  _!4 = !- 4
  _!5 = !- 5

  0! = 0 -!
  1! = 1 -!
  2! = 2 -!
  3! = 3 -!
  4! = 4 -!
  5! = 5 -!

  _#0 = #- 0
  _#1 = #- 1
  _#2 = #- 2
  _#3 = #- 3
  _#4 = #- 4
  _#5 = #- 5

  0# = 0 -#
  1# = 1 -#
  2# = 2 -#
  3# = 3 -#
  4# = 4 -#
  5# = 5 -#

  private
    postulate   -- Demo
      a b c d e : A
      p : a == b
      q : b == c
      r : c == d
      s : d == e

    t : PathSeq a e
    t =
      a =⟪ p ⟫
      b =⟪idp⟫
      b =⟪ q ⟫
      c =⟪ idp ⟫
      c =⟪ r ⟫
      d =⟪ s ⟫
      e =⟪idp⟫
      e ∎∎

    t' : a == e
    t' = ↯
      a =⟪ p ⟫
      b =⟪ q ⟫
      c =⟪ idp ⟫
      c =⟪ r ⟫
      d =⟪ s ⟫
      e ∎∎

    ex0 : t' == (↯ t)
    ex0 = idp

    ex1 : t' == p ∙ q ∙ r ∙ s
    ex1 = idp

    ex2 : (↯ t !1) == p ∙ q ∙ r
    ex2 = idp

    ex3 : (↯ t !3) == p ∙ q  -- The [idp] count
    ex3 = idp

    ex4 : (↯ 2! t) == r ∙ s
    ex4 = idp

    ex5 : (↯ 4! t) == s
    ex5 = idp

    ex6 : (↯ t #1) == s
    ex6 = idp

    ex7 : (↯ t #3) == r ∙ s
    ex7 = idp

    ex8 : (↯ 2# t) == p ∙ q
    ex8 = idp

    ex9 : (↯ 4# t) == p ∙ q ∙ r
    ex9 = idp



apd= : ∀ {i j} {A : Type i} {B : A → Type j} {f g : Π A B}
       (p : (x : A) → f x == g x) {a b : A} (q : a == b)
       → apd f q ▹ p b == p a ◃ apd g q
apd= {B = B} p {b} idp = idp▹ {B = B} (p b) ∙ ! (◃idp {B = B} (p b))

apd=-red : ∀ {i j} {A : Type i} {B : A → Type j} {f g : Π A B}
           (p : (x : A) → f x == g x) {a b : A} (q : a == b)
           {u : B b} (s : g b =-= u)
           → apd f q ▹ (↯ _ =⟪ p b ⟫ s) == p a ◃ (apd g q ▹ (↯ s))
apd=-red {B = B} p {b} idp s = coh (p b) s  where

  coh : ∀ {i} {A : Type i} {u v w : A} (p : u == v) (s : v =-= w)
    → (idp ∙' (↯ _ =⟪ p ⟫ s)) == p ∙ idp ∙' (↯ s)
  coh idp (a ∎∎) = idp
  coh idp (a =⟪ p₁ ⟫ s₁) = idp
