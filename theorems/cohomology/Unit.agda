{-# OPTIONS --without-K #-}

open import HoTT
open import groups.Exactness
open import cohomology.Theory

module cohomology.Unit {i} (CT : CohomologyTheory i) where

open CohomologyTheory CT

module _ (n : ℤ) where

  private
    ⊙LU = ⊙Lift {j = i} ⊙Unit

  ⊙Cof-Lift-Unit-equiv-Lift-Unit : ⊙Cof (⊙idf ⊙LU) ⊙≃ ⊙LU
  ⊙Cof-Lift-Unit-equiv-Lift-Unit = ≃-to-⊙≃ {X = _ , cfbase} e idp
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
    (Cid n ⊙LU , λ x → lemma₂ x ∙ app= (ap GroupHom.f (CF-ident n)) x)
    where
    lemma₁ : (x : CEl n (⊙Cof (⊙idf _)))
      → Cid n ⊙LU == CF n (⊙cfcod' (⊙idf _)) x
    lemma₁ x = ! (itok (C-exact n (⊙idf _)) _ [ x , idp ])
               ∙ app= (ap GroupHom.f (CF-ident n))
                      (CF n (⊙cfcod' (⊙idf _)) x)

    lemma₂ : (x : CEl n ⊙LU) → Cid n ⊙LU == CF n (⊙idf _) x
    lemma₂ = transport
      {A = Σ (Ptd i) (λ X → fst (⊙LU ⊙→ X))}
      (λ {(X , H) → (c : CEl n X) → Cid n ⊙LU == CF n H c})
      (pair= (⊙ua ⊙Cof-Lift-Unit-equiv-Lift-Unit)
             (prop-has-all-paths-↓ (⊙→-level (Lift-level Unit-is-prop))))
      lemma₁

  C-Unit : C n ⊙LU ≃ᴳ 0ᴳ
  C-Unit = contr-iso-0ᴳ _ C-Unit-is-contr
