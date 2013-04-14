{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.Connected

{-
    Wedge is a pushout.
-}

module Homotopy.Wedge
  where

  import Homotopy.Pushout as P

  record wedge-diag i : Set (suc i) where
    constructor diag_,_,_,_
    field
      A : Set i
      B : Set i
      a : A
      b : B

    f : unit {i} → A
    f _ = a
    g : unit {i} → B
    g _ = b

  wedge-diag-to-pushout-diag : ∀ {i} → wedge-diag i → P.pushout-diag i
  wedge-diag-to-pushout-diag {i} (diag A , B , a , b) = P.diag A , B , unit {i} , (λ _ → a) , (λ _ → b)

  wedge : ∀ {i} → wedge-diag i → Set i
  wedge d = P.pushout (wedge-diag-to-pushout-diag d)

  left : ∀ {i} {d : wedge-diag i} → wedge-diag.A d → wedge d
  left = P.left

  right : ∀ {i} {d : wedge-diag i} → wedge-diag.B d → wedge d
  right = P.right

  glue : ∀ {i} {d : wedge-diag i} → left (wedge-diag.a d) ≡ right (wedge-diag.b d)
  glue = P.glue tt

  wedge-rec : ∀ {i} {d : wedge-diag i}
    → let open wedge-diag d in
    ∀ {j} (P : wedge d → Set j)
    (left* : ∀ a → P (left a))
    (right* : ∀ b → P (right b))
    (glue* : transport P glue (left* a) ≡ right* b)
    → (∀ x → P x)
  wedge-rec P left* right* glue* = P.pushout-rec P left* right* (λ _ → glue*)

  wedge-rec-nondep : ∀ {i} {d : wedge-diag i}
    → let open wedge-diag d in
    ∀ {j} (P : Set j)
    (left* : ∀ a → P)
    (right* : ∀ b → P)
    (glue* : left* a ≡ right* b)
    → (wedge d → P)
  wedge-rec-nondep P left* right* glue* = P.pushout-rec-nondep P left* right* (λ _ → glue*)

{-
  module _ (f : X → Y) where
  nA (A-is-conn : is-connected n A)
  nB (B-is-conn : is-connected n B)
  (P : A → B → Set k)
  ⦃ P-is-trunc : ∀ a b → is-connected (n +2+ m) (P a b) ⦄
    extension : 
-}
