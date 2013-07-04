{-# OPTIONS --without-K #-}

open import lib.Base
open import lib.PathGroupoid
open import lib.Equivalences

module lib.Univalence where

coe-∙ : ∀ {i} {A B C : Type i} (p : A == B) (q : B == C) (a : A)
  → coe (p ∙ q) a == coe q (coe p a)
coe-∙ idp q a = idp

abstract
  idf-is-equiv : ∀ {i} (A : Type i) → is-equiv (idf A)
  idf-is-equiv A =
    record {g = idf A; f-g = λ _ → idp; g-f = λ _ → idp; adj = λ _ → idp }

coe-is-equiv : ∀ {i} {A B : Type i} (p : A == B) → is-equiv (coe p)
coe-is-equiv idp = idf-is-equiv _

ide : ∀ {i} (A : Type i) → A ≃ A
ide A = (idf A , idf-is-equiv A)

coe-equiv : ∀ {i} {A B : Type i} → A == B → A ≃ B
coe-equiv p = (coe p , coe-is-equiv p)

postulate  -- Univalence axiom
  ua : ∀ {i} {A B : Type i} → (A ≃ B) → A == B
  coe-equiv-β : ∀ {i} {A B : Type i} (e : A ≃ B) → coe-equiv (ua e) == e
  ua-η : ∀ {i} {A B : Type i} (p : A == B) → ua (coe-equiv p) == p

ua-equiv : ∀ {i} {A B : Type i} → (A ≃ B) ≃ (A == B)
ua-equiv = equiv ua coe-equiv ua-η coe-equiv-β

postulate -- TODO
  coe-β : ∀ {i} {A B : Type i} (e : A ≃ B) (a : A)
    → coe (ua e) a == –> e a
  coe!-β : ∀ {i} {A B : Type i} (e : A ≃ B) (b : B)
    → coe! (ua e) b == <– e b

coe-ap-! : ∀ {i j} {A : Type i} (P : A → Type j) {a b : A} (p : a == b)
  (x : P b)
  → coe (ap P (! p)) x == coe! (ap P p) x
coe-ap-! P idp x = idp

postulate
  ↓-idf-ua-out : ∀ {i} {A B : Type i} (e : A ≃ B) {u : A} {v : B}
    → u == v [ (λ x → x) ↓ (ua e) ]
    → –> e u == v

  ↓-idf-ua-in : ∀ {i} {A B : Type i} (e : A ≃ B) {u : A} {v : B}
    → –> e u == v
    → u == v [ (λ x → x) ↓ (ua e) ]

-- Induction along equivalences

equiv-induction : ∀ {i j} (P : {A B : Type i} (f : A ≃ B) → Type j)
  (d : (A : Type i) → P (ide A)) {A B : Type i} (f : A ≃ B)
  → P f
equiv-induction {i} {j} P d f =
  transport P (coe-equiv-β f)
    (equiv-induction-int P d (ua f)) where

  equiv-induction-int : ∀ {j}
    (P : {A : Type i} {B : Type i} (f : A ≃ B) → Type j)
    (d : (A : Type i) → P (ide A)) {A B : Type i} (p : A == B)
    → P (coe-equiv p)
  equiv-induction-int P d idp = d _
