{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Paths

module lib.types.Torus where

{-
data Torus : Type₀ where
  baseT : Torus
  loopT1 : baseT == baseT
  loopT2 : baseT == baseT
  surfT : loopT1 ∙ loopT2 == loopT2 ∙' loopT1
-}

private
  data #Torus : Type₀ where
    #baseT : #Torus

Torus : Type₀
Torus = #Torus

baseT : Torus
baseT = #baseT

postulate  -- HIT
  loopT1 : baseT == baseT
  loopT2 : baseT == baseT
  surfT : loopT1 ∙ loopT2 == loopT2 ∙' loopT1

{- Dependent elimination and computation rules -}
module _ {i} {A : Torus → Type i} (baseT* : A baseT)
  (loopT1* : baseT* == baseT* [ A ↓ loopT1 ])
  (loopT2* : baseT* == baseT* [ A ↓ loopT2 ])
  (surfT* : loopT1* ∙dep loopT2* == loopT2* ∙'dep loopT1*
              [ (λ p → baseT* == baseT* [ A ↓ p ]) ↓ surfT ]) where

  Torus-elim : Π Torus A
  Torus-elim #baseT = baseT*

  postulate  -- HIT
    loopT1-β : apd Torus-elim loopT1 == loopT1*
    
    loopT2-β : apd Torus-elim loopT2 == loopT2*

  private
    lhs : apd Torus-elim (loopT1 ∙ loopT2) == loopT1* ∙dep loopT2*
    lhs =
      apd Torus-elim (loopT1 ∙ loopT2)                   =⟨ apd-∙ Torus-elim loopT1 loopT2 ⟩
      apd Torus-elim loopT1 ∙dep apd Torus-elim loopT2   =⟨ loopT1-β |in-ctx (λ u → u ∙dep apd Torus-elim loopT2) ⟩
      loopT1* ∙dep apd Torus-elim loopT2                 =⟨ loopT2-β |in-ctx (λ u → loopT1* ∙dep u) ⟩
      loopT1* ∙dep loopT2* ∎

    rhs : apd Torus-elim (loopT2 ∙' loopT1) == loopT2* ∙'dep loopT1*
    rhs =
      apd Torus-elim (loopT2 ∙' loopT1)                   =⟨ apd-∙' Torus-elim loopT2 loopT1 ⟩
      apd Torus-elim loopT2 ∙'dep apd Torus-elim loopT1   =⟨ loopT2-β |in-ctx (λ u → u ∙'dep apd Torus-elim loopT1) ⟩
      loopT2* ∙'dep apd Torus-elim loopT1                 =⟨ loopT1-β |in-ctx (λ u → loopT2* ∙'dep u) ⟩
      loopT2* ∙'dep loopT1* ∎

  postulate  -- HIT
    surfT-β : apd (apd Torus-elim) surfT == lhs ◃ (surfT* ▹! rhs)

module _  {i} {A : Type i} (baseT* : A) (loopT1* loopT2* : baseT* == baseT*)
   (surfT* : loopT1* ∙ loopT2* == loopT2* ∙' loopT1*) where

  Torus-rec : Torus → A
  Torus-rec #baseT = baseT*

  postulate  -- HIT
    loopT1-β' : ap Torus-rec loopT1 == loopT1*
    loopT2-β' : ap Torus-rec loopT2 == loopT2*


  private
    lhs : ap Torus-rec (loopT1 ∙ loopT2) == loopT1* ∙ loopT2*
    lhs =
      ap Torus-rec (loopT1 ∙ loopT2)             =⟨ ap-∙ Torus-rec loopT1 loopT2 ⟩
      ap Torus-rec loopT1 ∙ ap Torus-rec loopT2  =⟨ loopT1-β' |in-ctx (λ u → u ∙ ap Torus-rec loopT2) ⟩
      loopT1* ∙ ap Torus-rec loopT2              =⟨ loopT2-β' |in-ctx (λ u → loopT1* ∙ u) ⟩
      loopT1* ∙ loopT2* ∎

    rhs : ap Torus-rec (loopT2 ∙' loopT1) == loopT2* ∙' loopT1*
    rhs =
      ap Torus-rec (loopT2 ∙' loopT1)             =⟨ ap-∙' Torus-rec loopT2 loopT1 ⟩
      ap Torus-rec loopT2 ∙' ap Torus-rec loopT1  =⟨ loopT2-β' |in-ctx (λ u → u ∙' ap Torus-rec loopT1) ⟩
      loopT2* ∙' ap Torus-rec loopT1              =⟨ loopT1-β' |in-ctx (λ u → loopT2* ∙' u) ⟩
      loopT2* ∙' loopT1* ∎

  postulate  -- HIT
    surfT-β' : ap (ap Torus-rec) surfT == lhs ∙ (surfT* ∙ (! rhs))
  -- One of them should be [_∙'_]
