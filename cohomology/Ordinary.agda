{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.KGn
open import cohomology.SuspAdjointLoopIso
open import cohomology.WithCoefficients

module cohomology.Ordinary where

module Ordinary {i} (G : Group i) (G-abelian : is-abelian G) where

  open Explicit G G-abelian

  C : (n : ℕ) → Ptd i → Group i
  C n X = →Ω-Group X (Ptd-KG (S n))

  {- Eilenberg-Steenrod Axioms -}

  {- Suspension Axiom -}
  C-Susp : (n : ℕ) (X : Ptd i) → C (S n) (Ptd-Susp X) == C n X
  C-Susp n X = 
    →Ω-Group (Ptd-Susp X) (Ptd-KG (S (S n)))
      =⟨ SuspAdjointLoopIso.iso X (Ptd-KG (S (S n))) ⟩
    →Ω-Group X (Ptd-Ω (Ptd-KG (S (S n))))
      =⟨ ap (→Ω-Group X) spec ⟩
    →Ω-Group X (Ptd-KG (S n)) ∎
    where
    spec : Ptd-Ω (Ptd-KG (S (S n))) == Ptd-KG (S n)
    spec = spectrum (S n)

