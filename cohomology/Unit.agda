{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.Exactness
open import cohomology.OrdinaryTheory

module cohomology.Unit {i} (OT : OrdinaryTheory i) where

open OrdinaryTheory OT

private
  PLU = Ptd-Lift {j = i} Ptd-Unit

  G : fst (Ptd-CEl O (Ptd-Cof (ptd-idf _)) ∙→ Ptd-CEl O PLU)
  G = CF O (ptd-cfcod (ptd-idf _))

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


  C₀-Unit-is-contr : is-contr (CEl O PLU)
  C₀-Unit-is-contr =
    (Cid O PLU , λ x → lemma₂ x ∙ app= (ap GroupHom.f (CF-ident O)) x)
    where
    lemma₁ : (x : CEl O (Ptd-Cof (ptd-idf _))) → Cid O PLU == fst G x
    lemma₁ x = ! (itok (C-exact O (ptd-idf _)) (fst G x) [ x , idp ])
               ∙ app= (ap GroupHom.f (CF-ident O)) (fst G x)

    lemma₂ : (x : CEl O PLU) → Cid O PLU == fst (CF O (ptd-idf _)) x
    lemma₂ = transport
      {A = Σ (Ptd i) (λ X → fst (PLU ∙→ X))}
      (λ {(X , H) → (c : CEl O X) → Cid O PLU == fst (CF O H) c})
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

C-Unit-is-trivial : (n : ℤ) → C n PLU == LiftUnit-Group
C-Unit-is-trivial O =
  contr-iso-LiftUnit _ C₀-Unit-is-contr
C-Unit-is-trivial (pos O) =
  ap (C (pos O)) Unit-is-Susp-Unit ∙ C-Susp O PLU
  ∙ (contr-iso-LiftUnit _ C₀-Unit-is-contr)
C-Unit-is-trivial (pos (S m)) =
  ap (C (pos (S m))) Unit-is-Susp-Unit ∙ C-Susp (pos m) PLU
  ∙ C-Unit-is-trivial (pos m)
C-Unit-is-trivial (neg O) =
  ! (C-Susp (neg O) PLU) ∙ ! (ap (C O) Unit-is-Susp-Unit)
  ∙ (contr-iso-LiftUnit _ C₀-Unit-is-contr)
C-Unit-is-trivial (neg (S m)) =
  ! (C-Susp (neg (S m)) PLU) ∙ ! (ap (C (neg m)) Unit-is-Susp-Unit)
  ∙ C-Unit-is-trivial (neg m)

C-Unit-is-contr : (n : ℤ) → is-contr (CEl n PLU)
C-Unit-is-contr n =
  transport (is-contr ∘ Group.El) (! (C-Unit-is-trivial n))
            (Lift-level Unit-is-contr)

C-Unit-is-prop : (n : ℤ) → is-prop (CEl n PLU)
C-Unit-is-prop n =
  transport (is-prop ∘ Group.El) (! (C-Unit-is-trivial n))
            (Lift-level Unit-is-prop)
