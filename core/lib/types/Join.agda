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

module _ {i j} {A : Type i} {B : Type j} where
  jleft : A → A * B
  jleft = left

  jright : B → A * B
  jright = right

  jglue : ∀ a b → jleft a == jright b
  jglue = curry glue

  module JoinElim {k} {P : A * B → Type k}
    (jleft* : (a : A) → P (jleft a)) (jright* : (b : B) → P (jright b))
    (jglue* : ∀ a b → jleft* a == jright* b [ P ↓ jglue a b ]) where

    private
      module M = PushoutElim {d = *-span A B} {P = P} jleft* jright* (uncurry jglue*)
    f = M.f
    glue-β = curry M.glue-β

  Join-elim = JoinElim.f

  module JoinRec {k} {C : Type k}
    (jleft* : (a : A) → C) (jright* : (b : B) → C)
    (jglue* : ∀ a b → jleft* a == jright* b) where

    private
      module M = PushoutRec jleft* jright* (uncurry jglue*)
    f = M.f
    glue-β = curry M.glue-β

  Join-rec = JoinRec.f

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
