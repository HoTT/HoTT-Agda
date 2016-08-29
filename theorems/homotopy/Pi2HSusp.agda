{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.HSpace renaming (HSpaceStructure to HSS)
open import homotopy.WedgeExtension

module homotopy.Pi2HSusp where

module Pi2HSusp {i} (A : Type i) (gA : has-level 1 A)
  (cA : is-connected 0 A) (A-H : HSS A)
  where

  {- TODO this belongs somewhere else, but where? -}
  private
    Type=-ext : ∀ {i} {A B : Type i} (p q : A == B)
      → ((x : A) → coe p x == coe q x) → p == q
    Type=-ext p q α =
      ! (ua-η p)
      ∙ ap ua (pair= (λ= α) (prop-has-all-paths-↓ (is-equiv-is-prop (coe q))))
      ∙ ua-η q

  open HSS A-H
  open ConnectedHSpace A cA A-H

  P : Suspension A → Type i
  P x = Trunc 1 (north == x)

  module Codes = SuspensionRec A A (λ a → ua (μ-e-r-equiv a))

  Codes : Suspension A → Type i
  Codes = Codes.f

  Codes-level : (x : Suspension A) → has-level 1 (Codes x)
  Codes-level = Suspension-elim gA gA
    (λ _ → prop-has-all-paths-↓ has-level-is-prop)

  encode₀ : {x : Suspension A} → (north == x) → Codes x
  encode₀ α = transport Codes α e

  encode : {x : Suspension A} → P x → Codes x
  encode {x} = Trunc-rec (Codes-level x) encode₀

  decode' : A → P north
  decode' a = [ (merid a ∙ ! (merid e)) ]

  abstract
    transport-Codes-mer : (a a' : A)
      → transport Codes (merid a) a' == μ a a'
    transport-Codes-mer a a' =
      coe (ap Codes (merid a)) a'
        =⟨ Codes.merid-β a |in-ctx (λ w → coe w a') ⟩
      coe (ua (μ-e-r-equiv a)) a'
        =⟨ coe-β (μ-e-r-equiv a) a' ⟩
      μ a a' ∎

    transport-Codes-mer-e-! : (a : A)
      → transport Codes (! (merid e)) a == a
    transport-Codes-mer-e-! a =
      coe (ap Codes (! (merid e))) a
        =⟨ ap-! Codes (merid e) |in-ctx (λ w → coe w a) ⟩
      coe (! (ap Codes (merid e))) a
        =⟨ Codes.merid-β e |in-ctx (λ w → coe (! w) a) ⟩
      coe (! (ua (μ-e-r-equiv e))) a
        =⟨ Type=-ext (ua (μ-e-r-equiv e)) idp (λ x → coe-β _ x ∙ μ-e-l x)
          |in-ctx (λ w → coe (! w) a) ⟩
      coe (! idp) a ∎

  abstract
    encode-decode' : (a : A) → encode (decode' a) == a
    encode-decode' a =
      transport Codes (merid a ∙ ! (merid e)) e
        =⟨ trans-∙ {B = Codes} (merid a) (! (merid e)) e ⟩
      transport Codes (! (merid e)) (transport Codes (merid a) e)
        =⟨ transport-Codes-mer a e ∙ μ-e-r a
          |in-ctx (λ w → transport Codes (! (merid e)) w) ⟩
      transport Codes (! (merid e)) a
        =⟨ transport-Codes-mer-e-! a ⟩
      a ∎

  abstract
    homomorphism : (a a' : A)
      → Path {A = Trunc 1 (north == south)}
        [ merid (μ a a' ) ] [ merid a' ∙ ! (merid e) ∙ merid a ]
    homomorphism = WedgeExt.ext args
      where
      args : WedgeExt.args {a₀ = e} {b₀ = e}
      args = record {m = -2; n = -2; cA = cA; cB = cA;
        P = λ a a' → (_ , Trunc-level {n = 1} _ _);
        f = λ a →  ap [_] $
              merid (μ a e)
                =⟨ ap merid (μ-e-r a) ⟩
              merid a
                =⟨ ap (λ w → w ∙ merid a) (! (!-inv-r (merid e)))
                   ∙ ∙-assoc (merid e) (! (merid e)) (merid a)  ⟩
              merid e ∙ ! (merid e) ∙ merid a ∎;
        g = λ a' → ap [_] $
              merid (μ e a')
                =⟨ ap merid (μ-e-l a') ⟩
              merid a'
                =⟨ ! (∙-unit-r (merid a'))
                   ∙ ap (λ w → merid a' ∙ w) (! (!-inv-l (merid e))) ⟩
              merid a' ∙ ! (merid e) ∙ merid e ∎ ;
        p = ap (λ {(p₁ , p₂) → ap [_] $
              merid (μ e e) =⟨ p₁ ⟩
              merid e       =⟨ p₂ ⟩
              merid e ∙ ! (merid e) ∙ merid e ∎})
             (pair×= (ap (λ x → ap merid x) (! μ-coh)) (coh (merid e)))}
        where coh : {B : Type i} {b b' : B} (p : b == b')
                → ap (λ w → w ∙ p) (! (!-inv-r p)) ∙ ∙-assoc p (! p) p
                  == ! (∙-unit-r p) ∙ ap (λ w → p ∙ w) (! (!-inv-l p))
              coh idp = idp

  decode : {x : Suspension A} → Codes x → P x
  decode {x} = Suspension-elim {P = λ x → Codes x → P x}
                 decode'
                 (λ a → [ merid a ])
                 (λ a → ↓-→-from-transp (λ= $ STS a))
                 x
    where
    abstract
      STS : (a a' : A) → transport P (merid a) (decode' a')
                         == [ merid (transport Codes (merid a) a') ]
      STS a a' =
        transport P (merid a) [ merid a' ∙ ! (merid e) ]
          =⟨ transport-Trunc (north ==_) (merid a) _ ⟩
        [ transport (north ==_) (merid a) (merid a' ∙ ! (merid e)) ]
          =⟨ ap [_] (trans-pathfrom {A = Suspension A} (merid a) _) ⟩
        [ (merid a' ∙ ! (merid e)) ∙ merid a ]
          =⟨ ap [_] (∙-assoc (merid a') (! (merid e)) (merid a)) ⟩
        [ merid a' ∙ ! (merid e) ∙ merid a ]
          =⟨ ! (homomorphism a a') ⟩
        [ merid (μ a a') ]
          =⟨ ap ([_] ∘ merid) (! (transport-Codes-mer a a')) ⟩
        [ merid (transport Codes (merid a) a') ] ∎

  abstract
    decode-encode : {x : Suspension A} (tα : P x)
      → decode {x} (encode {x} tα) == tα
    decode-encode {x} = Trunc-elim
      {P = λ tα → decode {x} (encode {x} tα) == tα}
      (λ _ → =-preserves-level 1 Trunc-level)
      (J (λ y p → decode {y} (encode {y} [ p ]) == [ p ])
         (ap [_] (!-inv-r (merid e))))

  main-lemma-eq : Trunc 1 (north' A == north) ≃ A
  main-lemma-eq = equiv encode decode' encode-decode' decode-encode

  ⊙main-lemma : ⊙Trunc 1 (⊙Ω (⊙Susp (A , e))) ⊙≃ (A , e)
  ⊙main-lemma = ≃-to-⊙≃ main-lemma-eq idp

  abstract
    main-lemma-iso : Ω^S-group 0 (⊙Trunc 1 (⊙Ω (⊙Susp (A , e)))) Trunc-level
                  ≃ᴳ Ω^S-group 0 (⊙Trunc 1 (A , e)) Trunc-level
    main-lemma-iso = (record {f = f; pres-comp = pres-comp} , ie)
      where
      h : fst (⊙Trunc 1 (⊙Ω (⊙Susp (A , e)))
            ⊙→ ⊙Trunc 1 (A , e))
      h = (λ x → [ encode x ]) , idp

      f : Ω (⊙Trunc 1 (⊙Ω (⊙Susp (A , e)))) → Ω (⊙Trunc 1 (A , e))
      f = Ω-fmap h

      pres-comp : (p q : Ω^ 1 (⊙Trunc 1 (⊙Ω (⊙Susp (A , e)))))
        → f (Ω^S-∙ 0 p q) == Ω^S-∙ 0 (f p) (f q)
      pres-comp = Ω^S-fmap-∙ 0 h

      ie : is-equiv f
      ie = Ω^-isemap 1 h (snd $ ((unTrunc-equiv A gA)⁻¹ ∘e main-lemma-eq))

  abstract
    π₂-Suspension : πS 1 (⊙Susp (A , e)) ≃ᴳ πS 0 (A , e)
    π₂-Suspension =
      πS 1 (⊙Susp (A , e))
        ≃ᴳ⟨ πS-Ω-split-iso 0 (⊙Susp (A , e)) ⟩
      πS 0 (⊙Ω (⊙Susp (A , e)))
        ≃ᴳ⟨ Ω^S-group-Trunc-fuse-diag-iso 0 (⊙Ω (⊙Susp (A , e))) ⁻¹ᴳ ⟩
      Ω^S-group 0 (⊙Trunc 1 (⊙Ω (⊙Susp (A , e)))) Trunc-level
        ≃ᴳ⟨ main-lemma-iso ⟩
      Ω^S-group 0 (⊙Trunc 1 (A , e)) Trunc-level
        ≃ᴳ⟨ Ω^S-group-Trunc-fuse-diag-iso 0 (A , e) ⟩
      πS 0 (A , e) ≃ᴳ∎
