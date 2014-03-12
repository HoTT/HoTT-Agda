{-# OPTIONS --without-K #-}

open import Base
open import Homotopy.PullbackDef

module Homotopy.PullbackIsPullback {i} (d : pullback-diag i) where

open pullback-diag d

import Homotopy.PullbackUP as PullbackUP
open PullbackUP d (λ _ → unit)

pullback-cone : cone (pullback d)
pullback-cone = (pullback.a d , pullback.b d , pullback.h d)

factor-pullback : (E : Set i) → (cone E → (E → pullback d))
factor-pullback E (top→A , top→B , h) x = (top→A x , top→B x , h x)

pullback-is-pullback : is-pullback (pullback d) pullback-cone
pullback-is-pullback E = iso-is-eq _
  (factor-pullback E)
  (λ y → refl)
  (λ f → refl)
