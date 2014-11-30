{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.SuspAdjointLoop
open import cohomology.WithCoefficients

module cohomology.SuspAdjointLoopIso where

module SuspAdjointLoopIso {i j} (X : Ptd i) (Y : Ptd j) where

  module ΣAΩ = SuspAdjointLoop X (⊙Ω Y)
  GSΣ = →Ω-group-structure (⊙Susp X) Y
  GSΩ = →Ω-group-structure X (⊙Ω Y)
  open GroupStructure

  comp-path : (p q : fst (⊙Ω (⊙Ω Y))) → ap2 _∙_ p q == p ∙ q
  comp-path p q = ap2-out _∙_ p q ∙ ap2 _∙_ (lemma p) (ap-idf q)
    where
    lemma : ∀ {i} {A : Type i} {x y : A} {p q : x == y} (α : p == q)
      → ap (λ r → r ∙ idp) α == ∙-unit-r p ∙ α ∙' ! (∙-unit-r q)
    lemma {p = idp} idp = idp

  pres-comp-inner : (H₁ H₂ : fst (⊙Susp X ⊙→ ⊙Ω Y))
    → ΣAΩ.R (comp GSΣ H₁ H₂) == comp GSΩ (ΣAΩ.R H₁) (ΣAΩ.R H₂)
  pres-comp-inner H₁ H₂ =
    transport
       (λ {(op , op-path) →
          ΣAΩ.R (comp GSΣ H₁ H₂) ==
          transport (λ b → Σ (fst X → _) (λ h → h (snd X) == b)) op-path
            (ΣAΩ.comp-lift (snd X) idp idp op (ΣAΩ.R H₁) (ΣAΩ.R H₂))})
       (pair= (λ= (λ p → λ= (comp-path p)))
              {b = idp} {b' = idp} (↓-app=cst-in snd-path))
       (ΣAΩ.pres-comp _∙_ H₁ H₂)
    where
    snd-path : idp == ap (λ f → f idp idp) (λ= (λ p → λ= (comp-path p))) ∙ idp
    snd-path =
      idp
        =⟨ ! (app=-β (comp-path idp) idp) ⟩
      app= (λ= (comp-path idp)) idp
        =⟨ ap (λ q → app= q idp) (! (app=-β (λ p → λ= (comp-path p)) idp)) ⟩
      app= (app= (λ= (λ p → λ= (comp-path p))) idp) idp
        =⟨ ∘-ap (λ z → z idp) (λ z → z idp) (λ= (λ p → λ= (comp-path p))) ⟩
      ap (λ f → f idp idp) (λ= (λ p → λ= (comp-path p)))
        =⟨ ! (∙-unit-r _) ⟩
      ap (λ f → f idp idp) (λ= (λ p → λ= (comp-path p))) ∙ idp ∎

  iso : →Ω-Group (⊙Susp X) Y == →Ω-Group X (⊙Ω Y)
  iso = group-iso
    (record {
      f = f;
      pres-comp = λ F G →
        Trunc-elim
          {P = λ F → f (Trunc-fmap2 (comp GSΣ) F G)
                  == Trunc-fmap2 (comp GSΩ) (f F) (f G)}
          (λ _ → =-preserves-level _ Trunc-level)
          (λ F' → Trunc-elim
            {P = λ G → f (Trunc-fmap2 (comp GSΣ) [ F' ] G)
                    == Trunc-fmap2 (comp GSΩ) (f [ F' ]) (f G)}
            (λ _ → =-preserves-level _ Trunc-level)
            (λ G' → ap [_] (pres-comp-inner F' G'))
            G
            )
          F })
    (uncurry (is-equiv-Trunc ⟨0⟩) ΣAΩ.eqv)
    where
    f = Trunc-fmap ΣAΩ.R
