{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.Theory

module cohomology.Unit {i} (CT : CohomologyTheory i) where

open CohomologyTheory CT

private
  ⊙LU = ⊙Lift {j = i} ⊙Unit

  G : fst (⊙CEl O (⊙Cof (⊙idf _)) ⊙→ ⊙CEl O ⊙LU)
  G = CF O (⊙cfcod (⊙idf _))

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

  cfcod-is-idf : Path {A = Σ (Ptd i) (λ X → fst (⊙LU ⊙→ X))}
                      (⊙Cof (⊙idf _) , ⊙cfcod (⊙idf _))
                      (⊙LU , ⊙idf _)
  cfcod-is-idf =
    pair= Cof-Unit-is-Unit
          (prop-has-all-paths-↓ (⊙→-level (Lift-level Unit-is-prop)))


  C₀-Unit-is-contr : is-contr (CEl O ⊙LU)
  C₀-Unit-is-contr =
    (Cid O ⊙LU , λ x → lemma₂ x ∙ app= (ap GroupHom.f (CF-ident O)) x)
    where
    lemma₁ : (x : CEl O (⊙Cof (⊙idf _))) → Cid O ⊙LU == fst G x
    lemma₁ x = ! (itok (C-exact O (⊙idf _)) (fst G x) [ x , idp ])
               ∙ app= (ap GroupHom.f (CF-ident O)) (fst G x)

    lemma₂ : (x : CEl O ⊙LU) → Cid O ⊙LU == fst (CF O (⊙idf _)) x
    lemma₂ = transport
      {A = Σ (Ptd i) (λ X → fst (⊙LU ⊙→ X))}
      (λ {(X , H) → (c : CEl O X) → Cid O ⊙LU == fst (CF O H) c})
      cfcod-is-idf
      lemma₁


  Unit-is-Susp-Unit : ⊙LU == ⊙Susp ⊙LU
  Unit-is-Susp-Unit = ⊙ua
    (equiv (λ _ → north _)
           (λ _ → lift unit)
           (Suspension-elim _
             {P = λ s → north _ == s}
             idp
             (merid _ (lift unit))
             (λ _ → ↓-cst=idf-in idp))
           (λ _ → idp))
    idp

C-Unit-is-trivial : (n : ℤ) → C n ⊙LU == LiftUnit-Group
C-Unit-is-trivial O =
  contr-is-0ᴳ _ C₀-Unit-is-contr
C-Unit-is-trivial (pos O) =
  ap (C (pos O)) Unit-is-Susp-Unit ∙ C-Susp O ⊙LU
  ∙ (contr-is-0ᴳ _ C₀-Unit-is-contr)
C-Unit-is-trivial (pos (S m)) =
  ap (C (pos (S m))) Unit-is-Susp-Unit ∙ C-Susp (pos m) ⊙LU
  ∙ C-Unit-is-trivial (pos m)
C-Unit-is-trivial (neg O) =
  ! (C-Susp (neg O) ⊙LU) ∙ ! (ap (C O) Unit-is-Susp-Unit)
  ∙ (contr-is-0ᴳ _ C₀-Unit-is-contr)
C-Unit-is-trivial (neg (S m)) =
  ! (C-Susp (neg (S m)) ⊙LU) ∙ ! (ap (C (neg m)) Unit-is-Susp-Unit)
  ∙ C-Unit-is-trivial (neg m)

C-Unit-is-contr : (n : ℤ) → is-contr (CEl n ⊙LU)
C-Unit-is-contr n =
  transport (is-contr ∘ Group.El) (! (C-Unit-is-trivial n))
            (Lift-level Unit-is-contr)

C-Unit-is-prop : (n : ℤ) → is-prop (CEl n ⊙LU)
C-Unit-is-prop n =
  transport (is-prop ∘ Group.El) (! (C-Unit-is-trivial n))
            (Lift-level Unit-is-prop)
