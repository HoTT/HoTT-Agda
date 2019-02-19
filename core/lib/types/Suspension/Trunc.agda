{-# OPTIONS --without-K --rewriting #-}

module lib.types.Suspension.Trunc where

open import lib.Basics
open import lib.NType2
open import lib.types.Paths
open import lib.types.Pointed
open import lib.types.Truncation

open import lib.types.Suspension.Core

module _ {i} (A : Type i) (m : ℕ₋₂) where

  module SuspTruncSwap =
    SuspRec
      {C = Trunc (S m) (Susp A)}
      [ north ]
      [ south ]
      (Trunc-rec
        {B = [ north ] == [ south ]}
        {{has-level-apply (Trunc-level {n = S m}) [ north ] [ south ]}}
        (λ x → ap [_] (merid x)))

  Susp-Trunc-swap : Susp (Trunc m A) → Trunc (S m) (Susp A)
  Susp-Trunc-swap = SuspTruncSwap.f

  Susp-Trunc-swap-Susp-fmap-trunc : ∀ (s : Susp A) →
    Susp-Trunc-swap (Susp-fmap [_] s) == [ s ]
  Susp-Trunc-swap-Susp-fmap-trunc =
    Susp-elim
      idp
      idp $
    λ a → ↓-='-in' $ ! $
    ap (Susp-Trunc-swap ∘ Susp-fmap [_]) (merid a)
      =⟨ ap-∘ Susp-Trunc-swap (Susp-fmap [_]) (merid a) ⟩
    ap Susp-Trunc-swap (ap (Susp-fmap [_]) (merid a))
      =⟨ ap (ap Susp-Trunc-swap) (SuspFmap.merid-β [_] a) ⟩
    ap Susp-Trunc-swap (merid [ a ])
      =⟨ SuspTruncSwap.merid-β [ a ] ⟩
    ap [_] (merid a) =∎

abstract
  Susp-Trunc-swap-natural : ∀ {i} {j} {A : Type i} {B : Type j} (f : A → B) (m : ℕ₋₂)
    → Susp-Trunc-swap B m ∘ Susp-fmap (Trunc-fmap f) ∼
      Trunc-fmap (Susp-fmap f) ∘ Susp-Trunc-swap A m
  Susp-Trunc-swap-natural {A = A} {B} f m =
    Susp-elim
      idp
      idp $
    Trunc-elim {{λ t → ↓-level (=-preserves-level Trunc-level)}} $ λ s →
    ↓-='-in' $
    ap (Trunc-fmap (Susp-fmap f) ∘ Susp-Trunc-swap A m) (merid [ s ])
      =⟨ ap-∘ (Trunc-fmap (Susp-fmap f)) (Susp-Trunc-swap A m) (merid [ s ]) ⟩
    ap (Trunc-fmap (Susp-fmap f)) (ap (Susp-Trunc-swap A m) (merid [ s ]))
      =⟨ ap (ap (Trunc-fmap (Susp-fmap f))) (SuspTruncSwap.merid-β A m [ s ]) ⟩
    ap (Trunc-fmap (Susp-fmap f)) (ap [_] (merid s))
      =⟨ ∘-ap (Trunc-fmap (Susp-fmap f)) [_] (merid s) ⟩
    ap ([_] ∘ Susp-fmap f) (merid s)
      =⟨ ap-∘ [_] (Susp-fmap f) (merid s) ⟩
    ap [_] (ap (Susp-fmap f) (merid s))
      =⟨ ap (ap [_]) (SuspFmap.merid-β f s) ⟩
    ap [_] (merid (f s))
      =⟨ ! (SuspTruncSwap.merid-β B m [ f s ]) ⟩
    ap (Susp-Trunc-swap B m) (merid [ f s ])
      =⟨ ap (ap (Susp-Trunc-swap B m)) (! (SuspFmap.merid-β (Trunc-fmap f) [ s ])) ⟩
    ap (Susp-Trunc-swap B m) (ap (Susp-fmap (Trunc-fmap f)) (merid [ s ]))
      =⟨ ∘-ap (Susp-Trunc-swap B m) (Susp-fmap (Trunc-fmap f)) (merid [ s ]) ⟩
    ap (Susp-Trunc-swap B m ∘ Susp-fmap (Trunc-fmap f)) (merid [ s ]) =∎

⊙Susp-Trunc-swap : ∀ {i} (A : Type i) (m : ℕ₋₂)
  → ⊙Susp (Trunc m A) ⊙→ ⊙Trunc (S m) (⊙Susp A)
⊙Susp-Trunc-swap A m = Susp-Trunc-swap A m , idp

abstract
  ⊙Susp-Trunc-swap-natural : ∀ {i} {j} {A : Type i} {B : Type j} (f : A → B) (m : ℕ₋₂)
    → ⊙Susp-Trunc-swap B m ⊙∘ ⊙Susp-fmap (Trunc-fmap f) ==
      ⊙Trunc-fmap (⊙Susp-fmap f) ⊙∘ ⊙Susp-Trunc-swap A m
  ⊙Susp-Trunc-swap-natural f m = ⊙λ=' (Susp-Trunc-swap-natural f m) idp
