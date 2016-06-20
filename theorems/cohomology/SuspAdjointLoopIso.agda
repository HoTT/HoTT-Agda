{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.PtdAdjoint
open import homotopy.SuspAdjointLoop
open import cohomology.WithCoefficients

module cohomology.SuspAdjointLoopIso where

module SuspAdjointLoopIso {i} where

  private
    hadj : HomAdjoint {i} {i} Σ⊣Ω.SuspFunctor Σ⊣Ω.LoopFunctor
    hadj = counit-unit-to-hom Σ⊣Ω.adj

    module A = HomAdjoint hadj

  module _ (X Y : Ptd i) where

    abstract
      pres-comp : (h₁ h₂ : fst (⊙Susp X ⊙→ ⊙Ω Y))
        → –> (A.eq X (⊙Ω Y)) (⊙conc ⊙∘ ⊙×-in h₁ h₂)
           == ⊙conc ⊙∘ ⊙×-in (–> (A.eq X (⊙Ω Y)) h₁) (–> (A.eq X (⊙Ω Y)) h₂)
      pres-comp h₁ h₂ =
        B.nat-cod h₁ h₂ ⊙conc
        ∙ ap (λ w → w ⊙∘ ⊙×-in (–> (A.eq X (⊙Ω Y)) h₁) (–> (A.eq X (⊙Ω Y)) h₂))
             arr2-lemma
        where
        module A× = RightAdjoint× hadj
        module B = RightAdjointBinary hadj

        ap2-lemma : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
          (f : A × B → C) {r s : A × B} (p : r == s)
          → ap f p == ap2 (curry f) (ap fst p) (ap snd p)
        ap2-lemma f idp = idp

        ⊙ap2-lemma : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
          (f : fst (X ⊙× Y ⊙→ Z))
          → ⊙ap f == ⊙ap2 f ⊙∘ ⊙×-in (⊙ap ⊙fst) (⊙ap ⊙snd)
        ⊙ap2-lemma (f , idp) = ⊙λ= (ap2-lemma f) idp

        arr2-lemma : B.arr2 ⊙conc == ⊙conc
        arr2-lemma =
          ⊙ap ⊙conc ⊙∘ A×.⊙out _ _
            =⟨ ⊙ap2-lemma ⊙conc |in-ctx (λ w → w ⊙∘ A×.⊙out _ _) ⟩
          (⊙ap2 ⊙conc ⊙∘ A×.⊙into _ _) ⊙∘ A×.⊙out _ _
            =⟨ ⊙∘-assoc (⊙ap2 ⊙conc) (A×.⊙into _ _) (A×.⊙out _ _) ⟩
          ⊙ap2 ⊙conc ⊙∘ (A×.⊙into _ _ ⊙∘ A×.⊙out _ _)
            =⟨ A×.⊙into-out _ _ |in-ctx (λ w → ⊙ap2 ⊙conc ⊙∘ w) ⟩
          ⊙ap2 ⊙conc
            =⟨ ⊙ap2-conc-is-conc ⟩
          ⊙conc ∎

    iso : →Ω-group (⊙Susp X) Y ≃ᴳ →Ω-group X (⊙Ω Y)
    iso = Trunc-group-iso
      (–> (A.eq X (⊙Ω Y))) pres-comp (snd (A.eq X (⊙Ω Y)))

  abstract
    nat-dom : {X Y : Ptd i} (f : fst (X ⊙→ Y)) (Z : Ptd i)
      → fst (iso X Z) ∘ᴳ →Ω-group-dom-act (⊙susp-fmap f) Z
        == →Ω-group-dom-act f (⊙Ω Z) ∘ᴳ fst (iso Y Z)
    nat-dom f Z = hom= _ _ $ λ= $ Trunc-elim
      (λ _ → =-preserves-level _ Trunc-level)
      (λ g → ap [_] (! (A.nat-dom f (⊙Ω Z) g)))
