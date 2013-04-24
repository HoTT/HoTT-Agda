{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Connected

module Homotopy.BlakersMassey.PushoutWrapper
  {i} {X Y : Set i} (Q : X → Y → Set i) where

  import Homotopy.Pushout as P

  module _ where
    private
      d : P.pushout-diag i
      d = record
        { A = X
        ; B = Y
        ; C = Σ X λ x → Σ Y (Q x)
        ; f = λ{( x , ( y , q )) → x}
        ; g = λ{( x , ( y , q )) → y}
        }

    P : Set i
    P = P.pushout d

    left : X → P
    left = P.left {d = d}

    right : Y → P
    right = P.right {d = d}

    glue : ∀ {x} {y} (q : Q x y) → left x ≡ right y
    glue {x} {y} q = P.glue {d = d} (x , (y , q))

    pushout-rec : ∀ {k} (R : P → Set k)
      (left* : ∀ x → R (left x)) (right* : ∀ y → R (right y))
      (glue* : ∀ {x} {y} (q : Q x y) → transport R (glue q) (left* x) ≡ right* y)
      → (∀ x → R x)
    pushout-rec R left* right* glue* =
      P.pushout-rec R left* right* (λ q → glue* (π₂ (π₂ q)))

    pushout-rec-nondep : ∀ {k} (R : Set k)
      (left* : X → R) (right* : Y → R)
      (glue* : ∀ {x} {y} (q : Q x y) → left* x ≡ right* y)
      → (P → R)
    pushout-rec-nondep R left* right* glue* =
      P.pushout-rec-nondep R left* right* (λ q → glue* (π₂ (π₂ q)))
