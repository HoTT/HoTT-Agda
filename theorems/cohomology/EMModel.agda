{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane
open import homotopy.EilenbergMacLaneFunctor
open import groups.ToOmega
open import cohomology.Theory
open import cohomology.SpectrumModel

module cohomology.EMModel where

module _ {i} (G : AbGroup i) where

  open EMExplicit G using (⊙EM; EM-level; EM-conn; spectrum)

  EM-E : (n : ℤ) → Ptd i
  EM-E (pos m) = ⊙EM m
  EM-E (negsucc m) = ⊙Lift ⊙Unit

  private

    E-spectrum : (n : ℤ) → ⊙Ω (EM-E (succ n)) ⊙≃ EM-E n
    E-spectrum (pos n) = spectrum n
    E-spectrum (negsucc O) = ≃-to-⊙≃ {X = ⊙Ω (EM-E 0)}
      (equiv (λ _ → _) (λ _ → idp)
             (λ _ → idp) (prop-has-all-paths {{has-level-apply (EM-level 0) _ _}} _))
      idp
    E-spectrum (negsucc (S n)) = ≃-to-⊙≃ {X = ⊙Ω (EM-E (negsucc n))}
      (equiv (λ _ → _) (λ _ → idp)
             (λ _ → idp) (prop-has-all-paths {{=-preserves-level ⟨⟩}} _))
      idp

  EM-Cohomology : CohomologyTheory i
  EM-Cohomology = spectrum-cohomology EM-E E-spectrum

  open CohomologyTheory EM-Cohomology

  EM-dimension : {n : ℤ} → n ≠ 0 → is-trivialᴳ (C n (⊙Lift ⊙S⁰))
  EM-dimension {pos O} neq = ⊥-rec (neq idp)
  EM-dimension {pos (S n)} _ =
    contr-is-trivialᴳ (C (pos (S n)) (⊙Lift ⊙S⁰))
      {{connected-at-level-is-contr
        {{⟨⟩}}
        {{Trunc-preserves-conn $
           equiv-preserves-conn
            (pre⊙∘-equiv ⊙lower-equiv ∘e ⊙Bool→-equiv-idf _ ⁻¹)
            {{path-conn (connected-≤T (⟨⟩-monotone-≤ (≤-ap-S (O≤ n)))
                                     )}}}}}}
  EM-dimension {negsucc O} _ =
    contr-is-trivialᴳ (C (negsucc O) (⊙Lift ⊙S⁰))
      {{Trunc-preserves-level 0 (Σ-level (Π-level λ _ →
        inhab-prop-is-contr idp {{has-level-apply (EM-level 0) _ _}})
        (λ x → has-level-apply (has-level-apply (EM-level 0) _ _) _ _))}}

  EM-dimension {negsucc (S n)} _ =
    contr-is-trivialᴳ (C (negsucc (S n)) (⊙Lift ⊙S⁰))
      {{Trunc-preserves-level 0 (Σ-level (Π-level λ _ →
        =-preserves-level ⟨⟩) λ _ → =-preserves-level (=-preserves-level ⟨⟩))}}

  EM-Ordinary : OrdinaryTheory i
  EM-Ordinary = ordinary-theory EM-Cohomology EM-dimension

module _ {i} (G : AbGroup i) (H : AbGroup i) (φ : G →ᴬᴳ H) where

  private
    module M {k} (A : AbGroup k) = CohomologyTheory (EM-Cohomology A)
    open M

  private
    EM-E-fmap : ∀ (n : ℤ) → EM-E G n ⊙→ EM-E H n
    EM-E-fmap (pos m) = ⊙EM-fmap G H φ m
    EM-E-fmap (negsucc m) = ⊙idf _

  EM-coeff-fmap : ∀ (X : Ptd i) (n : ℤ) → CEl G n X → CEl H n X
  EM-coeff-fmap X n = Trunc-fmap (⊙Ω-fmap (EM-E-fmap (succ n)) ⊙∘_)
