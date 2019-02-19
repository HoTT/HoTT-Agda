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

module _ {i} (G : AbGroup i) where

  open CohomologyTheory (spectrum-cohomology (EM-E G) (EM-spectrum G))
  open EMExplicit
  open import homotopy.SuspensionLoopSpaceInverse
  private
    module G = AbGroup G

  ⊙Ω-fmap-EM-E-fmap-inv-hom : ∀ (n : ℤ) → ⊙Ω-fmap (EM-E-fmap G G (inv-hom G) n) == ⊙Ω-!
  ⊙Ω-fmap-EM-E-fmap-inv-hom (negsucc n) =
    contr-center $ =-preserves-level $
    ⊙→-level (⊙Ω (⊙Lift ⊙Unit)) (⊙Ω (⊙Lift ⊙Unit)) $
    =-preserves-level $ Lift-level $ Unit-level
  ⊙Ω-fmap-EM-E-fmap-inv-hom (pos O) =
    prop-path
      (⊙→-level (⊙Ω (⊙EM G 0)) (⊙Ω (⊙EM G 0)) $
       has-level-apply (EM-level G 0) (pt (⊙EM G 0)) (pt (⊙EM G 0)))
      _ _
  ⊙Ω-fmap-EM-E-fmap-inv-hom (pos 1) = =⊙∘-out $
    ⊙Ω-fmap (⊙Trunc-fmap (⊙EM₁-fmap (inv-hom G))) ◃⊙idf
      =⊙∘⟨ 0 & 0 & !⊙∘ $ ⊙<–-inv-l-=⊙∘ (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ G.grp)) ⟩
    ⊙<– (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ G.grp)) ◃⊙∘
    ⊙–> (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ G.grp)) ◃⊙∘
    ⊙Ω-fmap (⊙Trunc-fmap (⊙EM₁-fmap (inv-hom G))) ◃⊙idf
      =⊙∘⟨ 1 & 2 & ⊙–>-⊙Ω-⊙Trunc-comm-natural-=⊙∘ 0 (⊙EM₁-fmap (inv-hom G)) ⟩
    ⊙<– (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ G.grp)) ◃⊙∘
    ⊙Trunc-fmap (⊙Ω-fmap (⊙EM₁-fmap (inv-hom G))) ◃⊙∘
    ⊙–> (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ G.grp)) ◃⊙idf
      =⊙∘₁⟨ 1 & 1 & ap ⊙Trunc-fmap $ ⊙Ω-fmap-⊙EM₁-neg G ⟩
    ⊙<– (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ G.grp)) ◃⊙∘
    ⊙Trunc-fmap ⊙Ω-! ◃⊙∘
    ⊙–> (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ G.grp)) ◃⊙idf
      =⊙∘⟨ 1 & 2 & =⊙∘-in
           {gs = ⊙–> (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ G.grp)) ◃⊙∘ ⊙Ω-! ◃⊙idf} $
           ! $ ⊙λ=' –>-=ₜ-equiv-pres-! idp ⟩
    ⊙<– (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ G.grp)) ◃⊙∘
    ⊙–> (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ G.grp)) ◃⊙∘
    ⊙Ω-! ◃⊙idf
      =⊙∘⟨ 0 & 2 & ⊙<–-inv-l-=⊙∘ (⊙Ω-⊙Trunc-comm 0 (⊙EM₁ G.grp)) ⟩
    ⊙Ω-! ◃⊙idf ∎⊙∘
  ⊙Ω-fmap-EM-E-fmap-inv-hom (pos (S (S k))) = =⊙∘-out $
    ⊙Ω-fmap (⊙EM-fmap G G (inv-hom G) (S (S k))) ◃⊙idf
      =⊙∘₁⟨ ap ⊙Ω-fmap (⊙EM-neg=⊙Trunc-fmap-⊙Susp-flip G k) ⟩
    ⊙Ω-fmap (⊙Trunc-fmap (⊙Susp-flip (⊙Susp^ k (⊙EM₁ G.grp)))) ◃⊙idf
      =⊙∘⟨ 0 & 0 & !⊙∘ $
           ⊙<–-inv-l-=⊙∘ (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ G.grp))) ⟩
    ⊙<– (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ G.grp))) ◃⊙∘
    ⊙–> (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ G.grp))) ◃⊙∘
    ⊙Ω-fmap (⊙Trunc-fmap (⊙Susp-flip (⊙Susp^ k (⊙EM₁ G.grp)))) ◃⊙idf
      =⊙∘⟨ 1 & 2 & ⊙–>-⊙Ω-⊙Trunc-comm-natural-=⊙∘ ⟨ S k ⟩
             (⊙Susp-flip (⊙Susp^ k (⊙EM₁ G.grp))) ⟩
    ⊙<– (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ G.grp))) ◃⊙∘
    ⊙Trunc-fmap (⊙Ω-fmap (⊙Susp-flip (⊙Susp^ k (⊙EM₁ G.grp)))) ◃⊙∘
    ⊙–> (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ G.grp))) ◃⊙idf
      =⊙∘₁⟨ 1 & 1 & ! $ ⊙Ω-!-⊙Susp-flip
              (⊙Susp^ k (⊙EM₁ G.grp))
              ⟨ S k ⟩
              (Spectrum.Trunc-fmap-σloop-is-equiv G k) ⟩
    ⊙<– (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ G.grp))) ◃⊙∘
    ⊙Trunc-fmap ⊙Ω-! ◃⊙∘
    ⊙–> (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ G.grp))) ◃⊙idf
      =⊙∘⟨ 1 & 2 & =⊙∘-in
           {gs = ⊙–> (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ G.grp))) ◃⊙∘
                 ⊙Ω-! ◃⊙idf} $
           ! $ ⊙λ=' –>-=ₜ-equiv-pres-! idp ⟩
    ⊙<– (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ G.grp))) ◃⊙∘
    ⊙–> (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ G.grp))) ◃⊙∘
    ⊙Ω-! ◃⊙idf
      =⊙∘⟨ 0 & 2 & ⊙<–-inv-l-=⊙∘ (⊙Ω-⊙Trunc-comm ⟨ S k ⟩ (⊙Susp^ (S k) (⊙EM₁ G.grp))) ⟩
    ⊙Ω-! ◃⊙idf ∎⊙∘

  EM-C-coeff-fmap-inv-hom : ∀ (n : ℤ) (X : Ptd i)
    → EM-C-coeff-fmap G G (inv-hom G) n X ==
      inv-hom (C-abgroup n X)
  EM-C-coeff-fmap-inv-hom n X =
    group-hom= $ λ= $ Trunc-elim $ λ h → ap [_]₀ $
    ap (_⊙∘ h) (⊙Ω-fmap-EM-E-fmap-inv-hom (succ n)) ∙
    ⊙λ=' (λ _ → idp) (∙-unit-r (ap ! (snd h)))
