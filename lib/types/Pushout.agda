{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Pi
open import lib.types.Pointed
open import lib.types.Sigma
open import lib.types.Span
open import lib.types.Paths
import lib.types.Generic1HIT as Generic1HIT

module lib.types.Pushout {i j k} where

module _ where

  private
    data #Pushout-aux (d : Span {i} {j} {k}) : Type (lmax (lmax i j) k) where
      #left : Span.A d → #Pushout-aux d
      #right : Span.B d → #Pushout-aux d

    data #Pushout (d : Span) : Type (lmax (lmax i j) k) where
      #pushout : #Pushout-aux d → (Unit → Unit) → #Pushout d

  Pushout : (d : Span) → Type _
  Pushout d = #Pushout d

  left : {d : Span} → Span.A d → Pushout d
  left a = #pushout (#left a) _

  right : {d : Span} → Span.B d → Pushout d
  right b = #pushout (#right b) _

  postulate  -- HIT
    glue : {d : Span} → (c : Span.C d) → left (Span.f d c) == right (Span.g d c) :> Pushout d

  module PushoutElim {d : Span} {l} {P : Pushout d → Type l}
    (left* : (a : Span.A d) → P (left a))
    (right* : (b : Span.B d) → P (right b))
    (glue* : (c : Span.C d) → left* (Span.f d c) == right* (Span.g d c) [ P ↓ glue c ]) where

    f : Π (Pushout d) P
    f = f-aux phantom  where

      f-aux : Phantom glue* → Π (Pushout d) P
      f-aux phantom (#pushout (#left y) _) = left* y
      f-aux phantom (#pushout (#right y) _) = right* y

    postulate  -- HIT
      glue-β : (c : Span.C d) → apd f (glue c) == glue* c

open PushoutElim public using () renaming (f to Pushout-elim)

module PushoutRec {d : Span} {l} {D : Type l}
  (left* : Span.A d → D) (right* : Span.B d → D)
  (glue* : (c : Span.C d) → left* (Span.f d c) == right* (Span.g d c)) where

  private
    module M = PushoutElim left* right* (λ c → ↓-cst-in (glue* c))

  f : Pushout d → D
  f = M.f

  glue-β : (c : Span.C d) → ap f (glue c) == glue* c
  glue-β c = apd=cst-in {f = f} (M.glue-β c)

module PushoutGeneric {d : Span {i} {j} {k}} where

  open Span d renaming (f to g; g to h)

  open Generic1HIT (Coprod A B) C (inl ∘ g) (inr ∘ h) public

  module _ where

    module To = PushoutRec (cc ∘ inl) (cc ∘ inr) pp

    to : Pushout d → T
    to = To.f

    from-cc : Coprod A B → Pushout d
    from-cc (inl a) = left a
    from-cc (inr b) = right b

    module From = Rec from-cc glue

    from : T → Pushout d
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
        to-from-pp c = ↓-∘=idf-in to from
          (ap to (ap from (pp c))   =⟨ From.pp-β c |in-ctx ap to ⟩
           ap to (glue c)           =⟨ To.glue-β c ⟩
           pp c ∎)

      from-to : (x : Pushout d) → from (to x) == x
      from-to = Pushout-elim (λ a → idp) (λ b → idp) (λ c → ↓-∘=idf-in from to
        (ap from (ap to (glue c))   =⟨ To.glue-β c |in-ctx ap from ⟩
         ap from (pp c)             =⟨ From.pp-β c ⟩
         glue c ∎))

  generic-pushout : Pushout d ≃ T
  generic-pushout = equiv to from to-from from-to

_⊔^[_]_/_ : (A : Type i) (C : Type k) (B : Type j)
  (fg : (C → A) × (C → B)) → Type (lmax (lmax i j) k)
A ⊔^[ C ] B  / (f , g) = Pushout (span A B C f g)

-- _*_ : ∀ {i j} (A : Type i) (B : Type j) → Type (lmax i j)
-- A * B = A ⊔^[ (A × B) ] B  / (fst , snd)

Ptd-Pushout : (d : Ptd-Span {i} {j} {k}) → Ptd _
Ptd-Pushout d = ∙[ Pushout (ptd-span-out d) , left (snd (Ptd-Span.X d)) ]

module _ (d : Ptd-Span {i} {j} {k}) where

  open Ptd-Span d

  ptd-left : fst (X ∙→ Ptd-Pushout d)
  ptd-left = (left , idp)

  ptd-right : fst (Y ∙→ Ptd-Pushout d)
  ptd-right =
    (right , ap right (! (snd g)) ∙ ! (glue (snd Z)) ∙' ap left (snd f))

  ptd-glue : (ptd-left ∘ptd f) == (ptd-right ∘ptd g)
  ptd-glue = pair=
    (λ= glue)
    (↓-app=cst-in $
      ap left (snd f) ∙ idp
        =⟨ ∙-unit-r _ ⟩
      ap left (snd f)
        =⟨ lemma (glue (snd Z)) (ap right (snd g)) (ap left (snd f)) ⟩
      glue (snd Z) ∙ ap right (snd g)
      ∙ ! (ap right (snd g)) ∙ ! (glue (snd Z)) ∙' ap left (snd f)
        =⟨ !-ap right (snd g)
           |in-ctx (λ w → glue (snd Z) ∙ ap right (snd g) ∙ w
                          ∙ ! (glue (snd Z)) ∙' ap left (snd f)) ⟩
      glue (snd Z) ∙ ap right (snd g)
      ∙ ap right (! (snd g)) ∙ ! (glue (snd Z)) ∙' ap left (snd f)
        =⟨ ! (app=-β glue (snd Z))
           |in-ctx (λ w → w ∙ ap right (snd g) ∙ ap right (! (snd g))
                            ∙ ! (glue (snd Z)) ∙' ap left (snd f)) ⟩
      app= (λ= glue) (snd Z) ∙ ap right (snd g)
      ∙ ap right (! (snd g)) ∙ ! (glue (snd Z)) ∙' ap left (snd f) ∎)
    where
    lemma : ∀ {i} {A : Type i} {x y z w : A}
      (p : x == y) (q : y == z) (r : x == w)
      → r == p ∙ q ∙ ! q ∙ ! p ∙' r
    lemma idp idp idp = idp

ptd-pushout-J : ∀ {l} (P : Ptd-Span → Type l)
  → ({A : Type i} {B : Type j} (Z : Ptd k) (f : fst Z → A) (g : fst Z → B)
     → P (ptd-span (A , f (snd Z)) (B , g (snd Z)) Z (f , idp) (g , idp)))
  → ((ps : Ptd-Span) → P ps)
ptd-pushout-J P t (ptd-span (_ , ._) (_ , ._) Z (f , idp) (g , idp)) = t Z f g

