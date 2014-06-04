{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Cospan
open import lib.types.Pointed

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
    idp ∎

  pullback-bβ : {a a' : A} (p : a == a') {b b' : B} (q : b == b')
    {h : f a == g b} {h' : f a' == g b'} (r : h ∙ ap g q == ap f p ∙ h')
    → ap Pullback.b (pullback= p q {h = h} {h' = h'} r) == q
  pullback-bβ idp idp r = 
    ap Pullback.b (ap (pullback _ _) (! (∙-unit-r _) ∙ r))
      =⟨ ∘-ap Pullback.b (pullback _ _) _ ⟩
    ap (λ _ → _) (! (∙-unit-r _) ∙ r)
      =⟨ ap-cst _ _ ⟩
    idp ∎

module _ {i j k} (D : Ptd-Cospan {i} {j} {k}) where

  Ptd-Pullback : Ptd (lmax i (lmax j k))
  Ptd-Pullback = 
    ∙[ Pullback (ptd-cospan-out D) , 
       pullback (snd X) (snd Y) (snd f ∙ ! (snd g)) ]
    where open Ptd-Cospan D
