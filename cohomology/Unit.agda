{-# OPTIONS --without-K #-}

open import HoTT
open import cohomology.OrdinaryTheory

module cohomology.Unit (OT : OrdinaryTheory lzero) where

open OrdinaryTheory OT

private
  G : fst (Ptd-CEl 0 (Ptd-Cof (idf _)) ∙→ Ptd-CEl 0 Ptd-Unit)
  G = CF 0 (ptd-cfcod (ptd-idf _))

  Cof-Unit-is-Unit : Ptd-Cof (idf Unit) == Ptd-Unit
  Cof-Unit-is-Unit = ptd-ua e idp
    where e = equiv (λ _ → unit)
                    (λ _ → cfbase (idf _))
                    (λ _ → idp)
                    (Cofiber-elim (idf _)
                       {P = λ c → cfbase (idf _) == c}
                       idp
                       (λ _ → cfglue (idf _) unit)
                       (λ _ → ↓-cst=idf-in idp))

  cfcod-is-idf : Path {A = Σ Ptd₀ (λ X → fst (Ptd-Unit ∙→ X))}
                      (Ptd-Cof (idf _) , ptd-cfcod (ptd-idf _)) 
                      (Ptd-Unit , ptd-idf _)
  cfcod-is-idf = 
    pair= Cof-Unit-is-Unit (prop-has-all-paths-↓ (∙→-level Unit-is-prop))


  C₀-Unit-is-contr : is-contr (CEl 0 Ptd-Unit)
  C₀-Unit-is-contr =
    (Cid 0 Ptd-Unit , λ x → lemma₂ x ∙ app= (ap GroupHom.f (CF-ident 0)) x)
    where
    lemma₁ : (x : CEl 0 (Ptd-Cof (idf _))) → Cid 0 Ptd-Unit == fst G x
    lemma₁ x = ! (C-exact-itok-mere 0 (ptd-idf _) (fst G x) [ x , idp ])
               ∙ app= (ap GroupHom.f (CF-ident 0)) (fst G x)

    lemma₂ : (x : CEl 0 Ptd-Unit) → Cid 0 Ptd-Unit == fst (CF 0 (ptd-idf _)) x
    lemma₂ = transport
      {A = Σ Ptd₀ (λ X → fst (Ptd-Unit ∙→ X))}
      (λ {(X , H) → (c : CEl 0 X) → Cid 0 Ptd-Unit == fst (CF 0 H) c})
      cfcod-is-idf
      lemma₁


  Unit-is-Susp-Unit : Ptd-Unit == Ptd-Susp Ptd-Unit
  Unit-is-Susp-Unit = ptd-ua 
    (equiv (λ _ → north _) 
           (λ _ → unit) 
           (Suspension-elim _
             {P = λ s → north _ == s}
             idp
             (merid _ unit)
             (λ _ → ↓-cst=idf-in idp))
           (λ _ → idp))
    idp

C-Unit-is-trivial : (n : ℕ) → C n Ptd-Unit == LiftUnit-Group
C-Unit-is-trivial O = 
  contr-iso-LiftUnit _ C₀-Unit-is-contr
C-Unit-is-trivial (S n) = 
  ap (C (S n)) Unit-is-Susp-Unit ∙ C-Susp n Ptd-Unit ∙ C-Unit-is-trivial n
