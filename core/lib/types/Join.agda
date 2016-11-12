{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Paths
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.PushoutFmap
open import lib.types.Sigma
open import lib.types.Span

module lib.types.Join  where

module _ {i j} (A : Type i) (B : Type j) where

  *-span : Span
  *-span = span A B (A × B) fst snd

  infix 80 _*_

  _*_ : Type _
  _*_ = Pushout *-span

module JoinElim {i j} {A : Type i} {B : Type j} {k} {P : A * B → Type k}
  (left* : (a : A) → P (left a)) (right* : (b : B) → P (right b))
  (glue* : (ab : A × B) → left* (fst ab) == right* (snd ab) [ P ↓ glue ab ])
  = PushoutElim left* right* glue*
open JoinElim public using () renaming (f to Join-elim)

module JoinRec {i j} {A : Type i} {B : Type j} {k} {D : Type k}
  (left* : (a : A) → D) (right* : (b : B) → D)
  (glue* : (ab : A × B) → left* (fst ab) == right* (snd ab))
  = PushoutRec left* right* glue*
open JoinRec public using () renaming (f to Join-rec)

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  ⊙*-span : ⊙Span
  ⊙*-span = ⊙span X Y (X ⊙× Y) ⊙fst ⊙snd

  infix 80 _⊙*_

  _⊙*_ : Ptd _
  _⊙*_ = ⊙Pushout ⊙*-span

module _ {i i' j j'} {A : Type i} {A' : Type i'} {B : Type j} {B' : Type j'}
  (eqA : A ≃ A') (eqB : B ≃ B') where

  *-span-emap : SpanEquiv (*-span A B) (*-span A' B')
  *-span-emap = ( span-map (fst eqA) (fst eqB) (×-fmap (fst eqA) (fst eqB)) (comm-sqr λ _ → idp) (comm-sqr λ _ → idp)
                , snd eqA , snd eqB , ×-isemap (snd eqA) (snd eqB))

  *-emap : A * B ≃ A' * B'
  *-emap = Pushout-emap *-span-emap

module _ {i i' j j'} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j} {Y' : Ptd j'} where

  ⊙*-emap : X ⊙≃ X' → Y ⊙≃ Y' → X ⊙* Y ⊙≃ X' ⊙* Y'
  ⊙*-emap ⊙eqX ⊙eqY = ≃-to-⊙≃ (*-emap (⊙≃-to-≃ ⊙eqX) (⊙≃-to-≃ ⊙eqY)) (ap left (snd (⊙–> ⊙eqX)))
