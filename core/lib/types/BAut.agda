{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.NConnected
open import lib.types.Nat
open import lib.types.Subtype
open import lib.types.Truncation

-- classifying types of automorphism groups of types
module lib.types.BAut where

BAut : ∀ {i} → Type i → Type (lsucc i)
BAut {i} A = Σ (Type i) λ X → Trunc -1 (A == X)

BAut-prop : ∀ {i} (A : Type i) → SubtypeProp (Type i) (lsucc i)
BAut-prop A = ((λ X → Trunc -1 (A == X)) , (λ X → Trunc-level))

pBAut : ∀ {i} → Type i → Ptd (lsucc i)
de⊙ (pBAut A) = BAut A
pt (pBAut A) = A , [ idp ]

BAut-trunc-path : ∀ {i} (A X : Type i) → (tp : Trunc -1 (A == X))
                  → Trunc -1 ((A , [ idp ]) == (X , tp) :> BAut A)
BAut-trunc-path {i} A X = Trunc-elim (λ p → Trunc-level)
                          λ p → [ pair= p (prop-has-all-paths-↓ Trunc-level) ]

BAut-conn : ∀ {i} (A : Type i) → is-connected 0 (BAut A)
fst (BAut-conn A) = [ pt (pBAut A) ]
snd (BAut-conn A) = Trunc-elim (λ x → raise-level (from-nat 0) Trunc-level [ A , [ idp ] ] x)
                               (λ { (X , tp) → <– (Trunc=-equiv [ A , [ idp ] ] [ X , tp ])
                                                  (BAut-trunc-path A X tp) })
