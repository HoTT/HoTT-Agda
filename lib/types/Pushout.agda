{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Span
open import lib.types.Paths
import lib.types.Generic1HIT as Generic1HIT

module lib.types.Pushout {i} {j} {k} where

private
  Spanijk = Span {i} {j} {k}

module Pushout {d : Spanijk} where

  open Span d renaming (f to g; g to h)

  module _ where

    private
      data #Pushout-aux : Type (lmax (lmax i j) k) where
        #left : A → #Pushout-aux
        #right : B → #Pushout-aux

      data #Pushout : Type (lmax (lmax i j) k) where
        #pushout : #Pushout-aux → (Unit → Unit) → #Pushout

    Pushout : Type _
    Pushout = #Pushout

    left : A → Pushout
    left a = #pushout (#left a) _

    right : B → Pushout
    right b = #pushout (#right b) _

    postulate  -- HIT
      glue : (c : C) → left (g c) == right (h c)

    module PushoutElim {l} {P : Pushout → Type l} (left* : (a : A) → P (left a))
      (right* : (b : B) → P (right b))
      (glue* : (c : C) → left* (g c) == right* (h c) [ P ↓ glue c ]) where

      f : Π Pushout P
      f = f-aux phantom  where

        f-aux : Phantom glue* → Π Pushout P
        f-aux phantom (#pushout (#left y) _) = left* y
        f-aux phantom (#pushout (#right y) _) = right* y

      postulate  -- HIT
        glue-β : (c : C) → apd f (glue c) == glue* c

  open PushoutElim public using () renaming (f to Pushout-elim)

  module PushoutRec {l} {D : Type l} (left* : A → D) (right* : B → D)
    (glue* : (c : C) → left* (g c) == right* (h c)) where

    private
      module M = PushoutElim left* right* (λ c → ↓-cst-in (glue* c))

    f : Pushout → D
    f = M.f

    glue-β : (c : C) → ap f (glue c) == glue* c
    glue-β c = apd=cst-in (M.glue-β c)

  module PushoutGeneric where

    open Generic1HIT (Coprod A B) C (inl ∘ g) (inr ∘ h) public

    generic-pushout : Pushout ≃ T
    generic-pushout = equiv to from to-from from-to  module _ where

      module To = PushoutRec (cc ∘ inl) (cc ∘ inr) pp

      to : Pushout → T
      to = To.f

      from-cc : Coprod A B → Pushout
      from-cc (inl a) = left a
      from-cc (inr b) = right b

      module From = Rec from-cc glue

      from : T → Pushout
      from = From.f

      abstract
        to-from : (x : T) → to (from x) == x
        to-from = elim to-from-cc to-from-pp where

          to-from-cc : (x : Coprod A B)
            → to (from (cc x)) == cc x
          to-from-cc (inl a) = idp
          to-from-cc (inr b) = idp

          to-from-pp :
            (c : C) → idp == idp [ (λ z → to (from z) == z) ↓ pp c ]
          to-from-pp c = ↓-∘=id-in from to
            (ap to (ap from (pp c))   =⟨ From.pp-β c |in-ctx ap to ⟩
            ap to (glue c)                    =⟨ To.glue-β c ⟩
            pp c ∎)

        from-to : (x : Pushout) → from (to x) == x
        from-to = Pushout-elim (λ a → idp) (λ b → idp) (λ c → ↓-∘=id-in to from
          (ap from (ap to (glue c))   =⟨ To.glue-β c |in-ctx ap from ⟩
          ap from (pp c)    =⟨ From.pp-β c ⟩
          glue c ∎))

open Pushout public hiding (Pushout)

Pushout : (d : Spanijk) → Type (lmax (lmax i j) k)
Pushout d = Pushout.Pushout {d = d}

_⊔^[_]_/_ : (A : Type i) (C : Type k) (B : Type j)
  (fg : (C → A) × (C → B)) → Type (lmax (lmax i j) k)
A ⊔^[ C ] B  / (f , g) = Pushout (span A B C f g)

-- _*_ : ∀ {i j} (A : Type i) (B : Type j) → Type (lmax i j)
-- A * B = A ⊔^[ (A × B) ] B  / (fst , snd)
