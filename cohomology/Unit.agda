{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.OrdinaryTheory

module cohomology.Unit {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT

private
  PLU = Ptd-Lift {j = i} Ptd-Unit

  G : fst (Ptd-CEl 0 (Ptd-Cof (ptd-idf _)) ∙→ Ptd-CEl 0 PLU)
  G = CF 0 (ptd-cfcod (ptd-idf _))

  Cof-Unit-is-Unit : Ptd-Cof (ptd-idf PLU) == PLU
  Cof-Unit-is-Unit = ptd-ua e idp
    where e = equiv (λ _ → lift unit)
                    (λ _ → cfbase (idf _))
                    (λ _ → idp)
                    (Cofiber-elim (idf _)
                       {P = λ c → cfbase (idf _) == c}
                       idp
                       (λ _ → cfglue (idf _) (lift unit))
                       (λ _ → ↓-cst=idf-in idp))

  cfcod-is-idf : Path {A = Σ (Ptd i) (λ X → fst (PLU ∙→ X))}
                      (Ptd-Cof (ptd-idf _) , ptd-cfcod (ptd-idf _))
                      (PLU , ptd-idf _)
  cfcod-is-idf =
    pair= Cof-Unit-is-Unit
          (prop-has-all-paths-↓ (∙→-level (Lift-level Unit-is-prop)))


  C₀-Unit-is-contr : is-contr (CEl 0 PLU)
  C₀-Unit-is-contr =
    (Cid 0 PLU , λ x → lemma₂ x ∙ app= (ap GroupHom.f (CF-ident 0)) x)
    where
    lemma₁ : (x : CEl 0 (Ptd-Cof (ptd-idf _))) → Cid 0 PLU == fst G x
    lemma₁ x = ! (itok (C-exact 0 (ptd-idf _)) (fst G x) [ x , idp ])
               ∙ app= (ap GroupHom.f (CF-ident 0)) (fst G x)

    lemma₂ : (x : CEl 0 PLU) → Cid 0 PLU == fst (CF 0 (ptd-idf _)) x
    lemma₂ = transport
      {A = Σ (Ptd i) (λ X → fst (PLU ∙→ X))}
      (λ {(X , H) → (c : CEl 0 X) → Cid 0 PLU == fst (CF 0 H) c})
      cfcod-is-idf
      lemma₁


  Unit-is-Susp-Unit : PLU == Ptd-Susp PLU
  Unit-is-Susp-Unit = ptd-ua
    (equiv (λ _ → north _)
           (λ _ → lift unit)
           (Suspension-elim _
             {P = λ s → north _ == s}
             idp
             (merid _ (lift unit))
             (λ _ → ↓-cst=idf-in idp))
           (λ _ → idp))
    idp

C-Unit-is-trivial : (n : ℕ) → C n PLU == LiftUnit-Group
C-Unit-is-trivial O =
  contr-iso-LiftUnit _ C₀-Unit-is-contr
C-Unit-is-trivial (S n) =
  ap (C (S n)) Unit-is-Susp-Unit ∙ C-SuspS n PLU ∙ C-Unit-is-trivial n

C-Unit-is-contr : (n : ℕ) → is-contr (CEl n PLU)
C-Unit-is-contr n =
  transport (is-contr ∘ Group.El) (! (C-Unit-is-trivial n))
            (Lift-level Unit-is-contr)

C-Unit-is-prop : (n : ℕ) → is-prop (CEl n PLU)
C-Unit-is-prop n =
  transport (is-prop ∘ Group.El) (! (C-Unit-is-trivial n))
            (Lift-level Unit-is-prop)
