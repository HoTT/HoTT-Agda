{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.KGn
open import cohomology.Theory
open import cohomology.SpectrumModel
open import cohomology.WithCoefficients

module cohomology.KGnModel
  {i} (G : Group i) (G-abelian : is-abelian G) where

open KGnExplicit G G-abelian using (⊙KG; KG-level; KG-conn; spectrum)

private
  E : (n : ℤ) → Ptd i
  E O = ⊙KG O
  E (pos m) = ⊙KG (S m)
  E (neg m) = ⊙Lift ⊙Unit

  E-spectrum : (n : ℤ) → ⊙Ω (E (succ n)) == E n
  E-spectrum O = spectrum O
  E-spectrum (pos n) = spectrum (S n)
  E-spectrum (neg O) =
    ⊙ua (equiv (λ _ → _) (λ _ → idp)
          (λ _ → idp) (prop-has-all-paths (KG-level _ _ _) _))
        idp
  E-spectrum (neg (S n)) =
    ⊙ua (equiv (λ _ → _) (λ _ → idp)
          (λ _ → idp) (prop-has-all-paths (Lift-level Unit-is-set _ _) _))
        idp

KG-Cohomology : CohomologyTheory i
KG-Cohomology = spectrum-cohomology E E-spectrum

open CohomologyTheory KG-Cohomology

KG-dimension : (n : ℤ) → n ≠ O → C n (⊙Sphere O) == 0G
KG-dimension O neq = ⊥-rec (neq idp)
KG-dimension (pos n) _ =
  contr-iso-LiftUnit _ $ connected-at-level-is-contr
    (Trunc-level {n = ⟨0⟩})
    (Trunc-preserves-conn ⟨0⟩
      (transport (λ B → is-connected ⟨0⟩ B)
        (! (Bool⊙→-path _))
        (path-conn (connected-≤T (⟨⟩-monotone-≤ (≤-ap-S (O≤ n)))
                                 (KG-conn (S n))))))
KG-dimension (neg O) _ =
  contr-iso-LiftUnit _ $ Trunc-preserves-level ⟨0⟩ $ ⊙→-level $
    inhab-prop-is-contr idp (KG-level O _ _)
KG-dimension (neg (S n)) _ =
  contr-iso-LiftUnit _ $ Trunc-preserves-level ⟨0⟩ $ ⊙→-level $
    Lift-level Unit-is-prop _ _

KG-Ordinary : OrdinaryTheory i
KG-Ordinary = ordinary-theory KG-Cohomology KG-dimension
