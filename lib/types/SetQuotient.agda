{-# OPTIONS --without-K #-}

open import lib.Basics

module lib.types.SetQuotient where

module _ {i} {A : Type i} {j} where

  private
    data #SetQuotient-aux (R : A → A → Type j) : Type i where
      #q[_] : A → #SetQuotient-aux R 

    data #SetQuotient (R : A → A → Type j) : Type i where
      #setquot : #SetQuotient-aux R → (Unit → Unit) → #SetQuotient R

  SetQuotient : (R : A → A → Type j) → Type i
  SetQuotient = #SetQuotient

  module _ {R : A → A → Type j} where

    q[_] : (a : A) → SetQuotient R
    q[ a ] = #setquot #q[ a ] _

    postulate  -- HIT
      quot-rel : {a₁ a₂ : A} → R a₁ a₂ → q[ a₁ ] == q[ a₂ ]

    postulate  -- HIT
      SetQuotient-level : is-set (SetQuotient R)

    SetQuotient-is-set = SetQuotient-level

    module SetQuotElim {k} {P : SetQuotient R → Type k}
      (p : (x : SetQuotient R) → is-set (P x)) (q[_]* : (a : A) → P q[ a ])
      (rel* : ∀ {a₁ a₂} (r : R a₁ a₂) → q[ a₁ ]* == q[ a₂ ]* [ P ↓ quot-rel r ]) where

      f : Π (SetQuotient R) P
      f = f-aux phantom phantom where

        f-aux : Phantom p
          → Phantom {A = ∀ {a₁ a₂} (r : R a₁ a₂) → _} rel*
          → Π (SetQuotient R) P
        f-aux phantom phantom (#setquot #q[ a ] _) = q[ a ]*

      postulate  -- HIT
        quot-rel-β : ∀ {a₁ a₂} (r : R a₁ a₂) → apd f (quot-rel r) == rel* r

open SetQuotElim public renaming (f to SetQuot-elim)

module SetQuotRec {i} {A : Type i} {j} {R : A → A → Type j} {k} {B : Type k} (p : is-set B)
  (q[_]* : A → B) (rel* : ∀ {a₁ a₂} (r : R a₁ a₂) → q[ a₁ ]* == q[ a₂ ]*) where

  private
    module M = SetQuotElim (λ x → p) q[_]* (λ {a₁ a₂} r → ↓-cst-in (rel* r))

  f : SetQuotient R → B
  f = M.f
