{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.Theory

module cohomology.Unit {i} (CT : CohomologyTheory i) where

open CohomologyTheory CT

module _ (n : ℤ) where

  private
    ⊙LU = ⊙Lift {j = i} ⊙Unit

  Cof-Unit-is-Unit : ⊙Cof (⊙idf ⊙LU) == ⊙LU
  Cof-Unit-is-Unit = ⊙ua e idp
    where e = equiv (λ _ → lift unit)
                    (λ _ → cfbase (idf _))
                    (λ _ → idp)
                    (Cofiber-elim (idf _)
                       {P = λ c → cfbase (idf _) == c}
                       idp
                       (λ _ → cfglue (idf _) (lift unit))
                       (λ _ → ↓-cst=idf-in idp))

  C-Unit-is-contr : is-contr (CEl n ⊙LU)
  C-Unit-is-contr =
    (Cid n ⊙LU , λ x → lemma₂ x ∙ app= (ap GroupHom.f (CF-ident n)) x)
    where
    lemma₁ : (x : CEl n (⊙Cof (⊙idf _)))
      → Cid n ⊙LU == fst (CF n (⊙cfcod (⊙idf _))) x
    lemma₁ x = ! (itok (C-exact n (⊙idf _)) _ [ x , idp ])
               ∙ app= (ap GroupHom.f (CF-ident n))
                      (fst (CF n (⊙cfcod (⊙idf _))) x)

    lemma₂ : (x : CEl n ⊙LU) → Cid n ⊙LU == fst (CF n (⊙idf _)) x
    lemma₂ = transport
      {A = Σ (Ptd i) (λ X → fst (⊙LU ⊙→ X))}
      (λ {(X , H) → (c : CEl n X) → Cid n ⊙LU == fst (CF n H) c})
      (pair= Cof-Unit-is-Unit
             (prop-has-all-paths-↓ (⊙→-level (Lift-level Unit-is-prop))))
      lemma₁

  C-Unit : C n ⊙LU == 0ᴳ
  C-Unit = contr-is-0ᴳ _ C-Unit-is-contr
