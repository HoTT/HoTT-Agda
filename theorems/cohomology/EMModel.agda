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

  EM-spectrum : (n : ℤ) → ⊙Ω (EM-E (succ n)) ⊙≃ EM-E n
  EM-spectrum (pos n) = spectrum n
  EM-spectrum (negsucc O) = ≃-to-⊙≃ {X = ⊙Ω (EM-E 0)}
    (equiv (λ _ → _) (λ _ → idp)
           (λ _ → idp) (prop-has-all-paths {{has-level-apply (EM-level 0) _ _}} _))
    idp
  EM-spectrum (negsucc (S n)) = ≃-to-⊙≃ {X = ⊙Ω (EM-E (negsucc n))}
    (equiv (λ _ → _) (λ _ → idp)
           (λ _ → idp) (prop-has-all-paths {{=-preserves-level ⟨⟩}} _))
    idp

  EM-Cohomology : CohomologyTheory i
  EM-Cohomology = spectrum-cohomology EM-E EM-spectrum

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

  EM-E-fmap : ∀ (n : ℤ) → EM-E G n ⊙→ EM-E H n
  EM-E-fmap (pos m) = ⊙EM-fmap G H φ m
  EM-E-fmap (negsucc m) = ⊙idf _

  open SpectrumModelMap (EM-E G) (EM-spectrum G) (EM-E H) (EM-spectrum H) EM-E-fmap
    public renaming (C-coeff-fmap to EM-C-coeff-fmap;
                     CEl-coeff-fmap to EM-CEl-coeff-fmap;
                     ⊙CEl-coeff-fmap to EM-⊙CEl-coeff-fmap)

module _ {i} (G : AbGroup i) where

  private
    EM-E-fmap-idhom : ∀ (n : ℤ)
      → EM-E-fmap G G (idhom (AbGroup.grp G)) n == ⊙idf _
    EM-E-fmap-idhom (pos n) = ⊙EM-fmap-idhom G n
    EM-E-fmap-idhom (negsucc n) = idp

  private
    module M = SpectrumModelMap (EM-E G) (EM-spectrum G) (EM-E G) (EM-spectrum G)

  EM-C-coeff-fmap-idhom : (n : ℤ) (X : Ptd i)
    → EM-C-coeff-fmap G G (idhom (AbGroup.grp G)) n X == idhom _
  EM-C-coeff-fmap-idhom n X =
    ap (λ map → M.C-coeff-fmap map n X) (λ= EM-E-fmap-idhom) ∙
    C-coeff-fmap-idf (EM-E G) (EM-spectrum G) n X

module _ {i} (G : AbGroup i) (H : AbGroup i) (K : AbGroup i)
             (ψ : H →ᴬᴳ K) (φ : G →ᴬᴳ H) where

  private
    EM-E-fmap-∘ : ∀ (n : ℤ)
      → EM-E-fmap G K (ψ ∘ᴳ φ) n == EM-E-fmap H K ψ n ⊙∘ EM-E-fmap G H φ n
    EM-E-fmap-∘ (pos n) = ⊙EM-fmap-∘ G H K ψ φ n
    EM-E-fmap-∘ (negsucc n) = idp

  private
    module M = SpectrumModelMap (EM-E G) (EM-spectrum G) (EM-E K) (EM-spectrum K)

  EM-C-coeff-fmap-∘ : (n : ℤ) (X : Ptd i)
    → EM-C-coeff-fmap G K (ψ ∘ᴳ φ) n X ==
      EM-C-coeff-fmap H K ψ n X ∘ᴳ
      EM-C-coeff-fmap G H φ n X
  EM-C-coeff-fmap-∘ n X =
    ap (λ map → M.C-coeff-fmap map n X) (λ= EM-E-fmap-∘) ∙
    C-coeff-fmap-∘ (EM-E G) (EM-spectrum G)
                   (EM-E H) (EM-spectrum H)
                   (EM-E K) (EM-spectrum K)
                   (EM-E-fmap H K ψ)
                   (EM-E-fmap G H φ)
                   n X