{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.EilenbergMacLane
open import cohomology.Theory
open import cohomology.SpectrumModel
open import cohomology.WithCoefficients

module cohomology.EMModel where

module _ {i} (G : AbGroup i) where

  open EMExplicit G using (⊙EM; EM-level; EM-conn; spectrum)

  private
    E : (n : ℤ) → Ptd i
    E (pos m) = ⊙EM m
    E (negsucc m) = ⊙Lift ⊙Unit

    E-spectrum : (n : ℤ) → ⊙Ω (E (succ n)) ⊙≃ E n
    E-spectrum (pos n) = spectrum n
    E-spectrum (negsucc O) = ≃-to-⊙≃ {X = ⊙Ω (E 0)}
      (equiv (λ _ → _) (λ _ → idp)
             (λ _ → idp) (prop-has-all-paths (EM-level _ _ _) _))
      idp
    E-spectrum (negsucc (S n)) = ≃-to-⊙≃ {X = ⊙Ω (E (negsucc n))}
      (equiv (λ _ → _) (λ _ → idp)
             (λ _ → idp) (prop-has-all-paths (Lift-level Unit-is-set _ _) _))
      idp

  EM-Cohomology : CohomologyTheory i
  EM-Cohomology = spectrum-cohomology E E-spectrum

  open CohomologyTheory EM-Cohomology

  EM-dimension : (n : ℤ) → n ≠ 0 → is-trivialᴳ (C n (⊙Lift ⊙S⁰))
  EM-dimension (pos O) neq = ⊥-rec (neq idp)
  EM-dimension (pos (S n)) _ =
    contr-is-trivialᴳ (C (pos (S n)) (⊙Lift ⊙S⁰)) $
      connected-at-level-is-contr
        (Trunc-level {n = 0})
        (Trunc-preserves-conn 0
          (equiv-preserves-conn
            (pre⊙∘-equiv ⊙lower-equiv ∘e ⊙Bool→-equiv-idf _ ⁻¹)
            (path-conn (connected-≤T (⟨⟩-monotone-≤ (≤-ap-S (O≤ n)))
                                     (EM-conn (S n))))))
  EM-dimension (negsucc O) _ =
    contr-is-trivialᴳ (C (negsucc O) (⊙Lift ⊙S⁰)) $
      Trunc-preserves-level 0 $ ⊙→-level $
        inhab-prop-is-contr idp (EM-level O _ _)
  EM-dimension (negsucc (S n)) _ =
    contr-is-trivialᴳ (C (negsucc (S n)) (⊙Lift ⊙S⁰)) $
      Trunc-preserves-level 0 $ ⊙→-level $
        Lift-level Unit-is-prop _ _

  EM-Ordinary : OrdinaryTheory i
  EM-Ordinary = ordinary-theory EM-Cohomology EM-dimension
