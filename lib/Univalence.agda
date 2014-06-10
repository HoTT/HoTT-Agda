{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.PathFunctor
open import lib.Equivalences
open import lib.PathOver

module lib.Univalence where

{-
The map [coe-equiv] is the map which is supposed to be an equivalence according
to the univalence axiom. We do not define it directly by path induction because
it may be helpful to know definitionally what are the components.
-}
coe-equiv : ∀ {i} {A B : Type i} → A == B → A ≃ B
coe-equiv p = (coe p , record { g = coe! p ; f-g = coe!-inv-r p ; g-f = coe!-inv-l p ; adj = coe-inv-adj p })

{- We postulate the univalence axiom as three separate axioms because it’s more
natural this way. But it doesn’t change anything in practice. -}

postulate  -- Univalence axiom
  ua : ∀ {i} {A B : Type i} → (A ≃ B) → A == B
  coe-equiv-β : ∀ {i} {A B : Type i} (e : A ≃ B) → coe-equiv (ua e) == e
  ua-η : ∀ {i} {A B : Type i} (p : A == B) → ua (coe-equiv p) == p

ua-equiv : ∀ {i} {A B : Type i} → (A ≃ B) ≃ (A == B)
ua-equiv = equiv ua coe-equiv ua-η coe-equiv-β

{- Reductions for coercions along a path constructed with the univalence axiom -}

coe-β : ∀ {i} {A B : Type i} (e : A ≃ B) (a : A)
  → coe (ua e) a == –> e a
coe-β e a = ap (λ e → –> e a) (coe-equiv-β e)

coe!-β : ∀ {i} {A B : Type i} (e : A ≃ B) (b : B)
  → coe! (ua e) b == <– e b
coe!-β e a = ap (λ e → <– e a) (coe-equiv-β e)

{- Paths over a path in a universe in the identity fibration reduces -}

↓-idf-ua-out : ∀ {i} {A B : Type i} (e : A ≃ B) {u : A} {v : B}
  → u == v [ (λ x → x) ↓ (ua e) ]
  → –> e u == v
↓-idf-ua-out e p = ! (coe-β e _) ∙ ↓-idf-out (ua e) p  where

↓-idf-ua-in : ∀ {i} {A B : Type i} (e : A ≃ B) {u : A} {v : B}
  → –> e u == v
  → u == v [ (λ x → x) ↓ (ua e) ]
↓-idf-ua-in e p = ↓-idf-in (ua e) (coe-β e _ ∙ p)  where

{- Induction along equivalences

If [P] is a predicate over all equivalences in a universe [Type i] and [d] is a
proof of [P] over all [ide A], then we get a section of [P]
-}

equiv-induction : ∀ {i j} (P : {A B : Type i} (f : A ≃ B) → Type j)
  (d : (A : Type i) → P (ide A)) {A B : Type i} (f : A ≃ B)
  → P f
equiv-induction {i} {j} P d f =
  transport P (coe-equiv-β f)
    (aux P d (ua f)) where

  aux : ∀ {j} (P : {A : Type i} {B : Type i} (f : A ≃ B) → Type j)
    (d : (A : Type i) → P (ide A)) {A B : Type i} (p : A == B)
    → P (coe-equiv p)
  aux P d idp = d _
