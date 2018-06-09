{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pi
open import lib.types.Pointed
open import lib.types.Sigma
open import lib.types.Span
open import lib.types.Paths
import lib.types.Generic1HIT as Generic1HIT

module lib.types.Pushout where

module _ {i j k} where

  postulate  -- HIT
    Pushout : (d : Span {i} {j} {k}) → Type (lmax (lmax i j) k)

  module _ {d : Span} where

    postulate  -- HIT
      left : Span.A d → Pushout d
      right : Span.B d → Pushout d
      glue : (c : Span.C d) → left (Span.f d c) == right (Span.g d c)

  module PushoutElim {d : Span} {l} {P : Pushout d → Type l}
    (left* : (a : Span.A d) → P (left a))
    (right* : (b : Span.B d) → P (right b))
    (glue* : (c : Span.C d) → left* (Span.f d c) == right* (Span.g d c) [ P ↓ glue c ]) where

    postulate  -- HIT
      f : Π (Pushout d) P
      left-β : ∀ a → f (left a) ↦ left* a
      right-β : ∀ b → f (right b) ↦ right* b
    {-# REWRITE left-β #-}
    {-# REWRITE right-β #-}

    postulate  -- HIT
      glue-β : (c : Span.C d) → apd f (glue c) == glue* c

Pushout-elim = PushoutElim.f

module PushoutRec {i j k} {d : Span {i} {j} {k}} {l} {D : Type l}
  (left* : Span.A d → D) (right* : Span.B d → D)
  (glue* : (c : Span.C d) → left* (Span.f d c) == right* (Span.g d c)) where

  abstract
    private
      module M = PushoutElim left* right* (λ c → ↓-cst-in (glue* c))

    f : Pushout d → D
    f = M.f

    left-β : ∀ a → f (left a) ↦ left* a
    left-β a = M.left-β a
    {-# REWRITE left-β #-}

    right-β : ∀ b → f (right b) ↦ right* b
    right-β b = M.right-β b
    {-# REWRITE right-β #-}

    glue-β : (c : Span.C d) → ap f (glue c) == glue* c
    glue-β c = apd=cst-in {f = f} (M.glue-β c)

Pushout-rec = PushoutRec.f

Pushout-rec-η : ∀ {i j k} {d : Span {i} {j} {k}} {l} {D : Type l} (f : Pushout d → D)
  → Pushout-rec (f ∘ left) (f ∘ right) (ap f ∘ glue) ∼ f
Pushout-rec-η f = Pushout-elim (λ _ → idp) (λ _ → idp)
  (λ c → ↓-='-in' $ ! $ PushoutRec.glue-β (f ∘ left) (f ∘ right) (ap f ∘ glue) c)

module PushoutGeneric {i j k} {d : Span {i} {j} {k}} where

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
        to-from-pp c = ↓-∘=idf-in' to from
          (ap to (ap from (pp c))   =⟨ From.pp-β c |in-ctx ap to ⟩
           ap to (glue c)           =⟨ To.glue-β c ⟩
           pp c =∎)

      from-to : (x : Pushout d) → from (to x) == x
      from-to = Pushout-elim (λ a → idp) (λ b → idp) (λ c → ↓-∘=idf-in' from to
        (ap from (ap to (glue c))   =⟨ To.glue-β c |in-ctx ap from ⟩
         ap from (pp c)             =⟨ From.pp-β c ⟩
         glue c =∎))

  generic-pushout : Pushout d ≃ T
  generic-pushout = equiv to from to-from from-to

_⊔^[_]_/_ : ∀ {i j k} (A : Type i) (C : Type k) (B : Type j)
  (fg : (C → A) × (C → B)) → Type (lmax (lmax i j) k)
A ⊔^[ C ] B  / (f , g) = Pushout (span A B C f g)

⊙Pushout : ∀ {i j k} (d : ⊙Span {i} {j} {k}) → Ptd _
⊙Pushout d = ⊙[ Pushout (⊙Span-to-Span d) , left (pt (⊙Span.X d)) ]

module _ {i j k} (d : ⊙Span {i} {j} {k}) where

  open ⊙Span d

  ⊙left : X ⊙→ ⊙Pushout d
  ⊙left = (left , idp)

  ⊙right : Y ⊙→ ⊙Pushout d
  ⊙right =
    (right , ap right (! (snd g)) ∙ ! (glue (pt Z)) ∙' ap left (snd f))

  ⊙glue : (⊙left ⊙∘ f) == (⊙right ⊙∘ g)
  ⊙glue = pair=
    (λ= glue)
    (↓-app=cst-in $
      ap left (snd f) ∙ idp
        =⟨ ∙-unit-r _ ⟩
      ap left (snd f)
        =⟨ lemma (glue (pt Z)) (ap right (snd g)) (ap left (snd f)) ⟩
      glue (pt Z) ∙ ap right (snd g)
      ∙ ! (ap right (snd g)) ∙ ! (glue (pt Z)) ∙' ap left (snd f)
        =⟨ !-ap right (snd g)
           |in-ctx (λ w → glue (pt Z) ∙ ap right (snd g) ∙ w
                          ∙ ! (glue (pt Z)) ∙' ap left (snd f)) ⟩
      glue (pt Z) ∙ ap right (snd g)
      ∙ ap right (! (snd g)) ∙ ! (glue (pt Z)) ∙' ap left (snd f)
        =⟨ ! (app=-β glue (pt Z))
           |in-ctx (λ w → w ∙ ap right (snd g) ∙ ap right (! (snd g))
                            ∙ ! (glue (pt Z)) ∙' ap left (snd f)) ⟩
      app= (λ= glue) (pt Z) ∙ ap right (snd g)
      ∙ ap right (! (snd g)) ∙ ! (glue (pt Z)) ∙' ap left (snd f) =∎)
    where
    lemma : ∀ {i} {A : Type i} {x y z w : A}
      (p : x == y) (q : y == z) (r : x == w)
      → r == p ∙ q ∙ ! q ∙ ! p ∙' r
    lemma idp idp idp = idp

⊙pushout-J : ∀ {i j k l} (P : ⊙Span → Type l)
  → ({A : Type i} {B : Type j} (Z : Ptd k) (f : de⊙ Z → A) (g : de⊙ Z → B)
     → P (⊙span ⊙[ A , f (pt Z) ] ⊙[ B , g (pt Z) ] Z (f , idp) (g , idp)))
  → ((ps : ⊙Span) → P ps)
⊙pushout-J P t (⊙span ⊙[ _ , ._ ] ⊙[ _ , ._ ] Z (f , idp) (g , idp)) = t Z f g
