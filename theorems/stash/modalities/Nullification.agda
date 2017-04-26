{-# OPTIONS --without-K --rewriting #-}

open import HoTT

open import stash.modalities.Orthogonality
open import stash.modalities.Modalities

module stash.modalities.Nullification where

module _ {i} where

  postulate -- HIT
    P⟨_⟩ : (A X : Type i) → Type i
    p[_] : {A X : Type i} → X → P⟨ A ⟩ X
    is-orth : {A X : Type i} → ⟦ A ⊥ P⟨ A ⟩ X ⟧

  module NullElim {A X : Type i} {Q : P⟨ A ⟩ X → Type i}
    (p : (x : P⟨ A ⟩ X) → ⟦ A ⊥ Q x ⟧) (d : (x : X) → Q p[ x ]) where

    postulate
      f : Π (P⟨ A ⟩ X) Q
      p[_]-β : ∀ x → f p[ x ] ↦ d x
    {-# REWRITE p[_]-β #-}

open NullElim public renaming (f to Null-elim)

module _ {i} (A : Type i) where

  NullModality : Modality i
  Modality.is-local NullModality X = ⟦ A ⊥ X ⟧
  Modality.is-local-is-prop NullModality = is-equiv-is-prop
  Modality.◯ NullModality = P⟨ A ⟩ 
  Modality.◯-is-local NullModality = is-orth
  Modality.η NullModality = p[_]
  Modality.◯-elim NullModality = Null-elim
  Modality.◯-elim-β NullModality _ _ _ = idp
  Modality.◯-=-is-local NullModality = {!!}

  -- Right, the last thing is to prove that path spaces
  -- are in fact null.

module _ {i} (A X : Type i) (x y : X) where

  to : P⟨ A ⟩ (x == y) → (Path {A = P⟨ Susp A ⟩ X} p[ x ] p[ y ])
  to = {!!}

  from : (Path {A = P⟨ Susp A ⟩ X} p[ x ] p[ y ]) → P⟨ A ⟩ (x == y)
  from p = {!!}

  thm : P⟨ A ⟩ (x == y) ≃ (Path {A = P⟨ Susp A ⟩ X} p[ x ] p[ y ])
  thm = {!!}



