{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.HSpace renaming (HSpaceStructure to HSS)
import homotopy.WedgeExtension as WedgeExt

module homotopy.Pi2HSusp {i} {X : Ptd i} {{_ : has-level 1 (de⊙ X)}}
  {{_ : is-connected 0 (de⊙ X)}} (H-X : HSS X)
  where

  {- TODO this belongs somewhere else, but where? -}
  private
    Type=-ext : ∀ {i} {A B : Type i} (p q : A == B)
      → (coe p ∼ coe q) → p == q
    Type=-ext p q α =
      ! (ua-η p)
      ∙ ap ua (Subtype=-out is-equiv-prop (λ= α))
      ∙ ua-η q

  module μ = ConnectedHSpace H-X
  μ = μ.μ
  private
    A = de⊙ X
    e = pt X

  P : Susp A → Type i
  P x = Trunc 1 (north == x)

  module Codes = SuspRec A A (λ a → ua (μ.r-equiv a))

  Codes : Susp A → Type i
  Codes = Codes.f

  Codes-level : (x : Susp A) → has-level 1 (Codes x)
  Codes-level = Susp-elim ⟨⟩ ⟨⟩
    (λ _ → prop-has-all-paths-↓)

  encode'₀ : {x : Susp A} → (north == x) → Codes x
  encode'₀ α = transport Codes α e

  encode' : {x : Susp A} → P x → Codes x
  encode' {x} = Trunc-rec {{Codes-level x}} encode'₀

  import homotopy.SuspAdjointLoop as SAL
  η : A → north == north
  η = fst (SAL.η X)

  decodeN' : A → P north
  decodeN' = [_] ∘ η

  abstract
    transport-Codes-mer : (a a' : A)
      → transport Codes (merid a) a' == μ a a'
    transport-Codes-mer a a' =
      coe (ap Codes (merid a)) a'
        =⟨ Codes.merid-β a |in-ctx (λ w → coe w a') ⟩
      coe (ua (μ.r-equiv a)) a'
        =⟨ coe-β (μ.r-equiv a) a' ⟩
      μ a a' ∎

    transport-Codes-mer-e-! : (a : A)
      → transport Codes (! (merid e)) a == a
    transport-Codes-mer-e-! a =
      coe (ap Codes (! (merid e))) a
        =⟨ ap-! Codes (merid e) |in-ctx (λ w → coe w a) ⟩
      coe (! (ap Codes (merid e))) a
        =⟨ Codes.merid-β e |in-ctx (λ w → coe (! w) a) ⟩
      coe (! (ua (μ.r-equiv e))) a
        =⟨ Type=-ext (ua (μ.r-equiv e)) idp (λ x → coe-β _ x ∙ μ.unit-l x)
          |in-ctx (λ w → coe (! w) a) ⟩
      coe (! idp) a ∎

  abstract
    encode'-decodeN' : (a : A) → encode' (decodeN' a) == a
    encode'-decodeN' a =
      transport Codes (merid a ∙ ! (merid e)) e
        =⟨ transp-∙ {B = Codes} (merid a) (! (merid e)) e ⟩
      transport Codes (! (merid e)) (transport Codes (merid a) e)
        =⟨ transport-Codes-mer a e ∙ μ.unit-r a
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
      args = record {m = -1; n = -1;
        P = λ a a' → (_ , ⟨⟩);
        f = λ a →  ap [_] $
              merid (μ a e)
                =⟨ ap merid (μ.unit-r a) ⟩
              merid a
                =⟨ ap (λ w → w ∙ merid a) (! (!-inv-r (merid e)))
                   ∙ ∙-assoc (merid e) (! (merid e)) (merid a)  ⟩
              merid e ∙ ! (merid e) ∙ merid a ∎;
        g = λ a' → ap [_] $
              merid (μ e a')
                =⟨ ap merid (μ.unit-l a') ⟩
              merid a'
                =⟨ ! (∙-unit-r (merid a'))
                   ∙ ap (λ w → merid a' ∙ w) (! (!-inv-l (merid e))) ⟩
              merid a' ∙ ! (merid e) ∙ merid e ∎ ;
        p = ap (λ {(p₁ , p₂) → ap [_] $
              merid (μ e e) =⟨ p₁ ⟩
              merid e       =⟨ p₂ ⟩
              merid e ∙ ! (merid e) ∙ merid e ∎})
             (pair×= (ap (λ x → ap merid x) (! μ.coh)) (coh (merid e)))}
        where coh : {B : Type i} {b b' : B} (p : b == b')
                → ap (λ w → w ∙ p) (! (!-inv-r p)) ∙ ∙-assoc p (! p) p
                  == ! (∙-unit-r p) ∙ ap (λ w → p ∙ w) (! (!-inv-l p))
              coh idp = idp

  decode' : {x : Susp A} → Codes x → P x
  decode' {x} = Susp-elim {P = λ x → Codes x → P x}
                 decodeN'
                 (λ a → [ merid a ])
                 (λ a → ↓-→-from-transp (λ= $ STS a))
                 x
    where
    abstract
      STS : (a a' : A) → transport P (merid a) (decodeN' a')
                         == [ merid (transport Codes (merid a) a') ]
      STS a a' =
        transport P (merid a) [ merid a' ∙ ! (merid e) ]
          =⟨ transport-Trunc (north ==_) (merid a) _ ⟩
        [ transport (north ==_) (merid a) (merid a' ∙ ! (merid e)) ]
          =⟨ ap [_] (transp-cst=idf {A = Susp A} (merid a) _) ⟩
        [ (merid a' ∙ ! (merid e)) ∙ merid a ]
          =⟨ ap [_] (∙-assoc (merid a') (! (merid e)) (merid a)) ⟩
        [ merid a' ∙ ! (merid e) ∙ merid a ]
          =⟨ ! (homomorphism a a') ⟩
        [ merid (μ a a') ]
          =⟨ ap ([_] ∘ merid) (! (transport-Codes-mer a a')) ⟩
        [ merid (transport Codes (merid a) a') ] ∎

  abstract
    decode'-encode' : {x : Susp A} (tα : P x)
      → decode' {x} (encode' {x} tα) == tα
    decode'-encode' {x} = Trunc-elim
      {P = λ tα → decode' {x} (encode' {x} tα) == tα}
      -- FIXME: Agda very slow (looping?) when omitting the next line
      {{λ _ → =-preserves-level Trunc-level}}
      (J (λ y p → decode' {y} (encode' {y} [ p ]) == [ p ])
         (ap [_] (!-inv-r (merid e))))

  eq' : Trunc 1 (Ω (⊙Susp X)) ≃ A
  eq' = equiv encode' decodeN' encode'-decodeN' decode'-encode'

  ⊙decodeN : ⊙Trunc 1 X ⊙→ ⊙Trunc 1 (⊙Ω (⊙Susp X))
  ⊙decodeN = ⊙Trunc-fmap (SAL.η X)

  decodeN : Trunc 1 A → Trunc 1 (Ω (⊙Susp X))
  decodeN = fst ⊙decodeN

  encodeN : Trunc 1 (Ω (⊙Susp X)) → Trunc 1 A
  encodeN = [_] ∘ encode' {x = north}

  eq : Trunc 1 (Ω (⊙Susp X)) ≃ Trunc 1 A
  eq = encodeN ,
    replace-inverse (snd ((unTrunc-equiv A)⁻¹ ∘e eq'))
      {decodeN}
      (Trunc-elim (λ _ → idp))

  ⊙eq : ⊙Trunc 1 (⊙Ω (⊙Susp X)) ⊙≃ ⊙Trunc 1 X
  ⊙eq = ≃-to-⊙≃ eq idp

  ⊙eq⁻¹ : ⊙Trunc 1 X ⊙≃ ⊙Trunc 1 (⊙Ω (⊙Susp X))
  ⊙eq⁻¹ = ⊙decodeN , snd (eq ⁻¹)

  iso : Ω^S-group 0 (⊙Trunc 1 (⊙Ω (⊙Susp X)))
      ≃ᴳ Ω^S-group 0 (⊙Trunc 1 X)
  iso = Ω^S-group-emap 0 ⊙eq

  abstract
    π₂-Susp : πS 1 (⊙Susp X) ≃ᴳ πS 0 X
    π₂-Susp =
      πS 1 (⊙Susp X)
        ≃ᴳ⟨ πS-Ω-split-iso 0 (⊙Susp X) ⟩
      πS 0 (⊙Ω (⊙Susp X))
        ≃ᴳ⟨ Ω^S-group-Trunc-fuse-diag-iso 0 (⊙Ω (⊙Susp X)) ⁻¹ᴳ ⟩
      Ω^S-group 0 (⊙Trunc 1 (⊙Ω (⊙Susp X)))
        ≃ᴳ⟨ iso ⟩
      Ω^S-group 0 (⊙Trunc 1 X)
        ≃ᴳ⟨ Ω^S-group-Trunc-fuse-diag-iso 0 X ⟩
      πS 0 X ≃ᴳ∎
