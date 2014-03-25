{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.Choice

module cohomology.OrdinaryTheory where

{- pointed version of the function [cfcod] from lib.types.Cofiber -}
ptd-cfcod : ∀ {j k} {X : Ptd j} {Y : Ptd k} (F : fst (X ∙→ Y))
  → fst (Y ∙→ Ptd-Cof (fst F))
ptd-cfcod {X = X} (f , fpt) = 
  (cfcod f , ap (cfcod f) (! fpt) ∙ ! (cfglue f (snd X)))

record OrdinaryTheory i : Type (lsucc i) where
  field
    C : ℕ → Ptd i → Group i

  CEl : ℕ → Ptd i → Type i
  CEl n X = Group.El (C n X)

  Cid : (n : ℕ) (X : Ptd i) → CEl n X
  Cid n X = GroupStructure.ident (Group.group-struct (C n X))

  Ptd-CEl : ℕ → Ptd i → Ptd i
  Ptd-CEl n X = ∙[ CEl n X , Cid n X ]

  field
    F-hom : (n : ℕ) {X Y : Ptd i} → fst (X ∙→ Y) → GroupHom (C n Y) (C n X)

  F : (n : ℕ) {X Y : Ptd i} → fst (X ∙→ Y) → fst (Ptd-CEl n Y ∙→ Ptd-CEl n X)
  F n f = (GroupHom.f (F-hom n f) , GroupHom.pres-ident (F-hom n f))

  field
    C-Susp : (n : ℕ) (X : Ptd i) → C (S n) (Ptd-Susp X) == C n X

    C-exact-itok-mere : (n : ℕ) {X Y : Ptd i} (f : fst (X ∙→ Y))
      → is-exact-itok-mere (F n (ptd-cfcod f)) (F n f)
    C-exact-ktoi-mere : (n : ℕ) {X Y : Ptd i} (f : fst (X ∙→ Y))
      → is-exact-ktoi-mere (F n (ptd-cfcod f)) (F n f)

    C-additive : (n : ℕ) {I : Type i} (Z : I → Ptd i)
      → ((W : I → Type i) → (∀ i → has-level ⟨ n ⟩ (W i)) → has-choice ⟨0⟩ I W)
      → C n (Ptd-BigWedge Z) == ΠG I (C n ∘ Z)

    C-dimensionS : (n : ℕ) 
      → C (S n) (Ptd-Lift Ptd-Bool) == LiftUnit-group


