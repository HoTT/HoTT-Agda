{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Theory

module cohomology.Unit {i} (CT : CohomologyTheory i) where

open CohomologyTheory CT

module _ (n : ℤ) where

  private
    ⊙LU = ⊙Lift {j = i} ⊙Unit

  ⊙Cofiber-Lift-Unit-equiv-Lift-Unit : ⊙Cof (⊙idf ⊙LU) ⊙≃ ⊙LU
  ⊙Cofiber-Lift-Unit-equiv-Lift-Unit = ≃-to-⊙≃ {X = _ , cfbase} e idp
    where
    e : Cofiber (idf (Lift {j = i} Unit)) ≃ Lift Unit
    e = equiv (λ _ → lift unit)
              (λ _ → cfbase)
              (λ _ → idp)
              (Cofiber-elim {f = idf _}
                 {P = λ c → cfbase == c}
                 idp
                 (λ _ → cfglue (lift unit))
                 (λ _ → ↓-cst=idf-in idp))

  C-Unit-is-contr : is-contr (CEl n ⊙LU)
  C-Unit-is-contr =
    (Cident n ⊙LU , λ x → lemma₂ x ∙ CEl-fmap-idf n x)
    where
    lemma₁ : (x : CEl n (⊙Cofiber (⊙idf _)))
      → Cident n ⊙LU == CEl-fmap n (⊙cfcod' (⊙idf _)) x
    lemma₁ x = ! (im-sub-ker (C-exact n (⊙idf _)) _ [ x , idp ])
               ∙ CEl-fmap-idf n (CEl-fmap n (⊙cfcod' (⊙idf _)) x)

    lemma₂ : (x : CEl n ⊙LU) → Cident n ⊙LU == CEl-fmap n (⊙idf _) x
    lemma₂ = transport
      {A = Σ (Ptd i) (λ X → ⊙LU ⊙→ X)}
      (λ {(X , H) → (c : CEl n X) → Cident n ⊙LU == CEl-fmap n H c})
      (pair= (⊙ua ⊙Cofiber-Lift-Unit-equiv-Lift-Unit)
             (prop-has-all-paths-↓ (⊙→-level (Lift-level Unit-is-prop))))
      lemma₁

  C-Unit : C n ⊙LU ≃ᴳ 0ᴳ
  C-Unit = contr-iso-0ᴳ _ C-Unit-is-contr
