{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType
open import lib.types.Cospan
open import lib.types.Pointed
open import lib.types.Sigma

module lib.types.Pullback where

module _ {i j k} (D : Cospan {i} {j} {k}) where

  open Cospan D

  record Pullback : Type (lmax i (lmax j k)) where
    constructor pullback
    field
      a : A
      b : B
      h : f a == g b

  pullback= : {a a' : A} (p : a == a') {b b' : B} (q : b == b')
    {h : f a == g b} {h' : f a' == g b'} (r : h ∙ ap g q == ap f p ∙ h')
    → pullback a b h == pullback a' b' h'
  pullback= idp idp r =
    ap (pullback _ _) (! (∙-unit-r _) ∙ r)

  pullback-aβ : {a a' : A} (p : a == a') {b b' : B} (q : b == b')
    {h : f a == g b} {h' : f a' == g b'} (r : h ∙ ap g q == ap f p ∙ h')
    → ap Pullback.a (pullback= p q {h = h} {h' = h'} r) == p
  pullback-aβ idp idp r =
    ap Pullback.a (ap (pullback _ _) (! (∙-unit-r _) ∙ r))
      =⟨ ∘-ap Pullback.a (pullback _ _) _ ⟩
    ap (λ _ → _) (! (∙-unit-r _) ∙ r)
      =⟨ ap-cst _ _ ⟩
    idp =∎

  pullback-bβ : {a a' : A} (p : a == a') {b b' : B} (q : b == b')
    {h : f a == g b} {h' : f a' == g b'} (r : h ∙ ap g q == ap f p ∙ h')
    → ap Pullback.b (pullback= p q {h = h} {h' = h'} r) == q
  pullback-bβ idp idp r =
    ap Pullback.b (ap (pullback _ _) (! (∙-unit-r _) ∙ r))
      =⟨ ∘-ap Pullback.b (pullback _ _) _ ⟩
    ap (λ _ → _) (! (∙-unit-r _) ∙ r)
      =⟨ ap-cst _ _ ⟩
    idp =∎

module _ {i j k} (D : ⊙Cospan {i} {j} {k}) where

  ⊙Pullback : Ptd (lmax i (lmax j k))
  ⊙Pullback =
    ⊙[ Pullback (⊙cospan-out D) ,
       pullback (pt X) (pt Y) (snd f ∙ ! (snd g)) ]
    where open ⊙Cospan D

module _ {i j k} (D : Cospan {i} {j} {k}) where
  open Cospan D

  pullback-decomp-equiv : Pullback D ≃ Σ (A × B) (λ {(a , b) → f a == g b})
  pullback-decomp-equiv = equiv
    (λ {(pullback a b h) → ((a , b) , h)})
    (λ {((a , b) , h) → pullback a b h})
    (λ _ → idp)
    (λ _ → idp)

module _ {i j k} (n : ℕ₋₂) {D : Cospan {i} {j} {k}} where
  open Cospan D

  pullback-level : has-level n A → has-level n B → has-level n C
    → has-level n (Pullback D)
  pullback-level pA pB pC =
    equiv-preserves-level ((pullback-decomp-equiv D)⁻¹) $
      Σ-level (×-level pA pB) (λ _ → =-preserves-level pC)
