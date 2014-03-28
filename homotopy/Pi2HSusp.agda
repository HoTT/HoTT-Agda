{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.HSpace renaming (HSpaceStructure to HSS)
open import homotopy.WedgeExtension

module homotopy.Pi2HSusp where

module Pi2HSusp {i} (A : Type i) (gA : has-level ⟨ 1 ⟩ A)
  (cA : is-connected ⟨0⟩ A) (A-H : HSS A) 
  (μcoh : HSS.μe- A-H (HSS.e A-H) == HSS.μ-e A-H (HSS.e A-H))
  where

  {- TODO this belongs somewhere else, but where? -}
  private
    Type=-ext : ∀ {i} {A B : Type i} (p q : A == B)
      → ((x : A) → coe p x == coe q x) → p == q
    Type=-ext p q α = 
      ! (ua-η p) 
      ∙ ap ua (pair= (λ= α) (prop-has-all-paths-↓ (is-equiv-is-prop (coe q))))
      ∙ ua-η q

  open HSpaceStructure A-H
  open ConnectedHSpace A cA A-H

  P : Suspension A → Type i
  P x = Trunc ⟨ 1 ⟩ (north A == x)

  Codes : Suspension A → Type i
  Codes = SuspensionRec.f A A A (λ a → ua (μ-equiv a))

  Codes-level : (x : Suspension A) → has-level ⟨ 1 ⟩ (Codes x)
  Codes-level = Suspension-elim A gA gA 
    (λ _ → prop-has-all-paths-↓ has-level-is-prop)

  encode₀ : {x : Suspension A} → (north A == x) → Codes x
  encode₀ α = transport Codes α e

  encode : {x : Suspension A} → P x → Codes x
  encode {x} = Trunc-rec (Codes-level x) encode₀

  decode' : A → P (north A)
  decode' a = [ (merid A a ∙ ! (merid A e)) ]

  abstract 
    transport-Codes-mer : (a a' : A) 
      → transport Codes (merid A a) a' == μ a a'
    transport-Codes-mer a a' = 
      coe (ap Codes (merid A a)) a' 
        =⟨ SuspensionRec.glue-β _ _ _ _ a |in-ctx (λ w → coe w a') ⟩ 
      coe (ua (μ-equiv a)) a'
        =⟨ coe-β (μ-equiv a) a' ⟩
      μ a a' ∎

    transport-Codes-mer-e-! : (a : A) 
      → transport Codes (! (merid A e)) a == a
    transport-Codes-mer-e-! a = 
      coe (ap Codes (! (merid A e))) a
        =⟨ ap-! Codes (merid A e) |in-ctx (λ w → coe w a) ⟩
      coe (! (ap Codes (merid A e))) a
        =⟨ SuspensionRec.glue-β _ _ _ _ e |in-ctx (λ w → coe (! w) a) ⟩
      coe (! (ua (μ-equiv e))) a
        =⟨ Type=-ext (ua (μ-equiv e)) idp (λ x → coe-β _ x ∙ μe- x) 
          |in-ctx (λ w → coe (! w) a) ⟩
      coe (! idp) a ∎

  abstract
    encode-decode' : (a : A) → encode (decode' a) == a
    encode-decode' a = 
      transport Codes (merid A a ∙ ! (merid A e)) e
        =⟨ trans-∙ {B = Codes} (merid A a) (! (merid A e)) e ⟩
      transport Codes (! (merid A e)) (transport Codes (merid A a) e)
        =⟨ transport-Codes-mer a e ∙ μ-e a
          |in-ctx (λ w → transport Codes (! (merid A e)) w) ⟩
      transport Codes (! (merid A e)) a
        =⟨ transport-Codes-mer-e-! a ⟩
      a ∎

  abstract 
    homomorphism : (a a' : A)
      → Path {A = Trunc ⟨ 1 ⟩ (north A == south A)}
        [ merid A (μ a a' ) ] [ merid A a' ∙ ! (merid A e) ∙ merid A a ]
    homomorphism = WedgeExt.ext args
      where
      args : WedgeExt.args {a₀ = e} {b₀ = e}
      args = record {m = ⟨-2⟩; n = ⟨-2⟩; cA = cA; cB = cA;
        P = λ a a' → (_ , Trunc-level {n = ⟨ 1 ⟩} _ _);
        f = λ a →  ap [_] $
              merid A (μ a e)
                =⟨ ap (merid A) (μ-e a) ⟩
              merid A a
                =⟨ ap (λ w → w ∙ merid A a) (! (!-inv-r (merid A e)))
                   ∙ ∙-assoc (merid A e) (! (merid A e)) (merid A a)  ⟩
              merid A e ∙ ! (merid A e) ∙ merid A a ∎;
        g = λ a' → ap [_] $
              merid A (μ e a')
                =⟨ ap (merid A) (μe- a') ⟩
              merid A a'
                =⟨ ! (∙-unit-r (merid A a'))
                   ∙ ap (λ w → merid A a' ∙ w) (! (!-inv-l (merid A e))) ⟩
              merid A a' ∙ ! (merid A e) ∙ merid A e ∎ ;
        p = ap (λ {(p₁ , p₂) → ap [_] $
              merid A (μ e e) =⟨ p₁ ⟩
              merid A e       =⟨ p₂ ⟩
              merid A e ∙ ! (merid A e) ∙ merid A e ∎})
             (pair×= (ap (λ x → ap (merid A) x) (! μcoh)) (coh (merid A e)))}
        where coh : {B : Type i} {b b' : B} (p : b == b')
                → ap (λ w → w ∙ p) (! (!-inv-r p)) ∙ ∙-assoc p (! p) p
                  == ! (∙-unit-r p) ∙ ap (λ w → p ∙ w) (! (!-inv-l p))
              coh idp = idp

  decode : {x : Suspension A} → Codes x → P x
  decode {x} = Suspension-elim A {P = λ x → Codes x → P x}
                 decode'
                 (λ a → [ merid A a ])
                 (λ a → coe (↓-→-is-square {B = Codes} {C = P} 
                               decode' (λ a → [ merid A a ]) _)
                            (λ= $ STS a))
                 x
    where 
    abstract
      STS : (a a' : A) → transport P (merid A a) (decode' a') 
                         == [ merid A (transport Codes (merid A a) a') ]
      STS a a' =
        transport P (merid A a) [ merid A a' ∙ ! (merid A e) ]
          =⟨ transport-Trunc (λ x → north A == x) (merid A a) _ ⟩
        [ transport (λ x → north A == x) (merid A a) (merid A a' ∙ ! (merid A e)) ]
          =⟨ ap [_] (trans-pathfrom {A = Suspension A} (merid A a) _) ⟩
        [ (merid A a' ∙ ! (merid A e)) ∙ merid A a  ]
          =⟨ ap [_] (∙-assoc (merid A a') (! (merid A e)) (merid A a)) ⟩
        [ merid A a' ∙ ! (merid A e) ∙ merid A a  ]
          =⟨ ! (homomorphism a a') ⟩
        [ merid A (μ a a') ]
          =⟨ ap ([_] ∘ merid A) (! (transport-Codes-mer a a')) ⟩
        [ merid A (transport Codes (merid A a) a') ] ∎

  abstract
    decode-encode : {x : Suspension A} (tα : P x) 
      → decode {x} (encode {x} tα) == tα
    decode-encode {x} = Trunc-elim 
      {B = λ tα → decode {x} (encode {x} tα) == tα}
      (λ _ → =-preserves-level ⟨ 1 ⟩ Trunc-level)
      (J (λ y p → decode {y} (encode {y} [ p ]) == [ p ])
         (ap [_] (!-inv-r (merid A e))))

  main-lemma-eqv : Trunc ⟨ 1 ⟩ (north A == north A) ≃ A
  main-lemma-eqv = equiv encode decode' encode-decode' decode-encode

  main-lemma : Trunc ⟨ 1 ⟩ (north A == north A) == A
  main-lemma = ua main-lemma-eqv

  ptd-main-lemma : Ptd-Trunc ⟨ 1 ⟩ (Ptd-Ω (Ptd-Susp (A , e))) == (A , e)
  ptd-main-lemma = ptd-ua main-lemma-eqv idp

  {- for main-lemma-iso; separated for performance reasons -}
  module Iso where
    abstract
      H : fst (Ptd-Trunc ⟨ 1 ⟩ (Ptd-Ω (Ptd-Susp (A , e)))
            ∙→ Ptd-Trunc ⟨ 1 ⟩ (A , e))
      H = (λ x → [ encode x ]) , idp

      F : fst (Ptd-Ω^ 1 (Ptd-Trunc ⟨ 1 ⟩ (Ptd-Ω (Ptd-Susp (A , e))))
            ∙→ Ptd-Ω^ 1 (Ptd-Trunc ⟨ 1 ⟩ (A , e)))
      F = ap^ 1 H

      f : Ω^ 1 (Ptd-Trunc ⟨ 1 ⟩ (Ptd-Ω (Ptd-Susp (A , e))))
        → Ω^ 1 (Ptd-Trunc ⟨ 1 ⟩ (A , e))
      f = fst F

      pres-ident : f (idp^ 1) == idp^ 1
      pres-ident = snd F

      pres-comp : (p q : Ω^ 1 (Ptd-Trunc ⟨ 1 ⟩ (Ptd-Ω (Ptd-Susp (A , e)))))
        → f (conc^ 1 p q) == conc^ 1 (f p) (f q)
      pres-comp = ap^-conc^ 1 H

      ie : is-equiv f
      ie = is-equiv-ap^ 1 H (snd $ ((unTrunc-equiv A gA)⁻¹ ∘e main-lemma-eqv))

  abstract
    main-lemma-iso : ⦃ p1 : 1 ≠ 0 ⦄ → 
         Ω^-Group 1 ⦃ p1 ⦄ (Ptd-Trunc ⟨ 1 ⟩ (Ptd-Ω (Ptd-Susp (A , e)))) Trunc-level
      == Ω^-Group 1 ⦃ p1 ⦄ (Ptd-Trunc ⟨ 1 ⟩ (A , e)) Trunc-level
    main-lemma-iso = group-iso 
      (record {f = f; pres-ident = pres-ident; pres-comp = pres-comp})
      ie 
      where open Iso

  abstract
    π₂-Suspension : ⦃ p1 : 1 ≠ 0 ⦄ → ⦃ p2 : 2 ≠ 0 ⦄ 
      → π 2 ⦃ p2 ⦄ (Ptd-Susp (A , e)) == π 1 ⦃ p1 ⦄ (A , e)
    π₂-Suspension ⦃ p1 ⦄ ⦃ p2 ⦄ = 
      π 2 ⦃ p2 ⦄ (Ptd-Susp (A , e))
        =⟨ π-inner-iso 1 ⦃ p1 ⦄ ⦃ p2 ⦄ (Ptd-Susp (A , e)) ⟩
      π 1 ⦃ p1 ⦄ (Ptd-Ω (Ptd-Susp (A , e)))
        =⟨ ! (π-Trunc-shift-iso 1 ⦃ p1 ⦄ (Ptd-Ω (Ptd-Susp (A , e)))) ⟩
      Ω^-Group 1 ⦃ p1 ⦄ (Ptd-Trunc ⟨ 1 ⟩ (Ptd-Ω (Ptd-Susp (A , e)))) Trunc-level
        =⟨ main-lemma-iso ⦃ p1 ⦄ ⟩
      Ω^-Group 1 ⦃ p1 ⦄ (Ptd-Trunc ⟨ 1 ⟩ (A , e)) Trunc-level
        =⟨ π-Trunc-shift-iso 1 ⦃ p1 ⦄ (A , e) ⟩
      π 1 ⦃ p1 ⦄ (A , e) ∎
