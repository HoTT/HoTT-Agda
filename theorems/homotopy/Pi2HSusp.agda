{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.HSpace renaming (HSpaceStructure to HSS)
open import homotopy.WedgeExtension

module homotopy.Pi2HSusp where

module Pi2HSusp {i} {X : Ptd i}
  {{_ : has-level 1 (de⊙ X)}}
  {{_ : is-connected 0 (de⊙ X)}}
  (H-X : HSS X) where

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

  back : south == north
  back = ! (merid e)

  private
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
      → transport Codes back a == a
    transport-Codes-mer-e-! a =
      coe (ap Codes back) a
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
      transport Codes (merid a ∙ back) e
        =⟨ transp-∙ {B = Codes} (merid a) back e ⟩
      transport Codes back (transport Codes (merid a) e)
        =⟨ transport-Codes-mer a e ∙ μ.unit-r a
          |in-ctx (λ w → transport Codes back w) ⟩
      transport Codes back a
        =⟨ transport-Codes-mer-e-! a ⟩
      a ∎

  add-path-and-inverse-l : ∀ {k} {B : Type k} {x y z : B}
    → (p : y == x) (q : y == z)
    → q == (p ∙ ! p) ∙ q
  add-path-and-inverse-l p q = ap (λ s → s ∙ q) (! (!-inv-r p))

  add-path-and-inverse-r : ∀ {k} {B : Type k} {x y z : B}
    → (p : x == y) (q : z == y)
    → p == (p ∙ ! q) ∙ q
  add-path-and-inverse-r p q =
    ! (∙-unit-r p) ∙ ap (λ s → p ∙ s) (! (!-inv-l q)) ∙ ! (∙-assoc p (! q) q)

  homomorphism-l : (a' : A) → merid (μ e a') == (merid a' ∙ back) ∙ merid e
  homomorphism-l a' = ap merid (μ.unit-l a') ∙ add-path-and-inverse-r (merid a') (merid e)

  homomorphism-r : (a : A) → merid (μ a e) == (merid e ∙ back) ∙ merid a
  homomorphism-r a = ap merid (μ.unit-r a) ∙ add-path-and-inverse-l (merid e) (merid a)

  homomorphism-l₁ : (a' : A) → [ merid (μ e a') ]₁ == [ (merid a' ∙ back) ∙ merid e ]₁
  homomorphism-l₁ = ap [_]₁ ∘ homomorphism-l

  homomorphism-r₁ : (a : A) → [ merid (μ a e) ]₁ == [ (merid e ∙ back) ∙ merid a ]₁
  homomorphism-r₁ = ap [_]₁ ∘ homomorphism-r

  abstract
    homomorphism-args : args {i} {i} {A} {e} {A} {e}
    homomorphism-args =
      record {
        m = -1; n = -1;
        P = λ a a' → (Q a a' , ⟨⟩);
        f = homomorphism-r₁;
        g = homomorphism-l₁;
        p = ap (λ {(p₁ , p₂) → ap [_] (ap merid p₁ ∙ p₂)})
               (pair×= (! μ.coh) (coh (merid e)))
      }
      where
        Q : A → A → Type i
        Q a a' = [ merid (μ a a' ) ]₁ == [ (merid a' ∙ back) ∙ merid a ]₁
        coh : {B : Type i} {b b' : B} (p : b == b')
          → add-path-and-inverse-l p p == add-path-and-inverse-r p p
        coh idp = idp

    module HomomorphismExt =
      WedgeExt {i} {i} {A} {e} {A} {e} homomorphism-args

    homomorphism : (a a' : A)
      → [ merid (μ a a' ) ]₁ == [ (merid a' ∙ back) ∙ merid a ]₁
    homomorphism = HomomorphismExt.ext

    homomorphism-β-l : (a' : A) → homomorphism e a' == homomorphism-l₁ a'
    homomorphism-β-l = HomomorphismExt.β-r

    homomorphism-β-r : (a : A) → homomorphism a e == homomorphism-r₁ a
    homomorphism-β-r = HomomorphismExt.β-l

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
        transport P (merid a) [ merid a' ∙ back ]
          =⟨ transport-Trunc' (north ==_) (merid a) _ ⟩
        [ transport (north ==_) (merid a) (merid a' ∙ back) ]
          =⟨ ap [_] (transp-cst=idf {A = Susp A} (merid a) _) ⟩
        [ (merid a' ∙ back) ∙ merid a ]
          =⟨ ! (homomorphism a a') ⟩
        [ merid (μ a a') ]
          =⟨ ap ([_] ∘ merid) (! (transport-Codes-mer a a')) ⟩
        [ merid (transport Codes (merid a) a') ] ∎

  decode'-encode' : {x : Susp A} (tα : P x)
    → decode' {x} (encode' {x} tα) == tα
  decode'-encode' {x} = Trunc-elim
    {P = λ tα → decode' {x} (encode' {x} tα) == tα}
    -- FIXME: Agda very slow (looping?) when omitting the next line
    {{λ _ → =-preserves-level Trunc-level}}
    (J (λ y p → decode' {y} (encode' {y} [ p ]) == [ p ])
        (ap [_] (!-inv-r (merid e))))

  eq' : Trunc 1 (Ω (⊙Susp (de⊙ X))) ≃ A
  eq' = equiv encode' decodeN' encode'-decodeN' decode'-encode'

  ⊙decodeN : ⊙Trunc 1 X ⊙→ ⊙Trunc 1 (⊙Ω (⊙Susp (de⊙ X)))
  ⊙decodeN = ⊙Trunc-fmap (SAL.η X)

  decodeN : Trunc 1 A → Trunc 1 (Ω (⊙Susp (de⊙ X)))
  decodeN = fst ⊙decodeN

  encodeN : Trunc 1 (Ω (⊙Susp (de⊙ X))) → Trunc 1 A
  encodeN = [_] ∘ encode' {x = north}

  ⊙encodeN : ⊙Trunc 1 (⊙Ω (⊙Susp (de⊙ X))) ⊙→ ⊙Trunc 1 X
  ⊙encodeN = encodeN , idp

  eq : Trunc 1 (Ω (⊙Susp (de⊙ X))) ≃ Trunc 1 A
  eq = encodeN ,
    replace-inverse (snd ((unTrunc-equiv A)⁻¹ ∘e eq'))
      {decodeN}
      (Trunc-elim (λ _ → idp))

  ⊙eq : ⊙Trunc 1 (⊙Ω (⊙Susp (de⊙ X))) ⊙≃ ⊙Trunc 1 X
  ⊙eq = ≃-to-⊙≃ eq idp

  abstract
    ⊙decodeN-⊙encodeN : ⊙decodeN ⊙∘ ⊙encodeN == ⊙idf _
    ⊙decodeN-⊙encodeN =
      ⊙λ=' {X = ⊙Trunc 1 (⊙Ω (⊙Susp (de⊙ X)))} {Y = ⊙Trunc 1 (⊙Ω (⊙Susp (de⊙ X)))}
           decode'-encode' $
      ↓-idf=cst-in $
      ! (∙-unit-r (ap [_] (!-inv-r (merid (pt X)))))

    ⊙<–-⊙eq : ⊙<– ⊙eq == ⊙decodeN
    ⊙<–-⊙eq =
      –>-is-inj (pre⊙∘-equiv {Z = ⊙Trunc 1 (⊙Ω (⊙Susp (de⊙ X)))} ⊙eq) (⊙<– ⊙eq) ⊙decodeN $
      (⊙<– ⊙eq) ⊙∘ ⊙encodeN
        =⟨ ⊙<–-inv-l ⊙eq ⟩
      ⊙idf _
        =⟨ ! ⊙decodeN-⊙encodeN ⟩
      ⊙decodeN ⊙∘ ⊙encodeN =∎

    ⊙encodeN-⊙decodeN : ⊙encodeN ⊙∘ ⊙decodeN == ⊙idf _
    ⊙encodeN-⊙decodeN =
      ⊙encodeN ⊙∘ ⊙decodeN
        =⟨ ap (⊙encodeN ⊙∘_) (! ⊙<–-⊙eq) ⟩
      ⊙encodeN ⊙∘ ⊙<– ⊙eq
        =⟨ ⊙<–-inv-r ⊙eq ⟩
      ⊙idf _ =∎

  ⊙eq⁻¹ : ⊙Trunc 1 X ⊙≃ ⊙Trunc 1 (⊙Ω (⊙Susp (de⊙ X)))
  ⊙eq⁻¹ = ⊙decodeN , snd (eq ⁻¹)

  iso : Ω^S-group 0 (⊙Trunc 1 (⊙Ω (⊙Susp (de⊙ X))))
      ≃ᴳ Ω^S-group 0 (⊙Trunc 1 X)
  iso = Ω^S-group-emap 0 ⊙eq

  abstract
    π₂-Susp : πS 1 (⊙Susp (de⊙ X)) ≃ᴳ πS 0 X
    π₂-Susp =
      πS 1 (⊙Susp (de⊙ X))
        ≃ᴳ⟨ πS-Ω-split-iso 0 (⊙Susp (de⊙ X)) ⟩
      πS 0 (⊙Ω (⊙Susp (de⊙ X)))
        ≃ᴳ⟨ Ω^S-group-Trunc-fuse-diag-iso 0 (⊙Ω (⊙Susp (de⊙ X))) ⁻¹ᴳ ⟩
      Ω^S-group 0 (⊙Trunc 1 (⊙Ω (⊙Susp (de⊙ X))))
        ≃ᴳ⟨ iso ⟩
      Ω^S-group 0 (⊙Trunc 1 X)
        ≃ᴳ⟨ Ω^S-group-Trunc-fuse-diag-iso 0 X ⟩
      πS 0 X ≃ᴳ∎

module Pi2HSuspNaturality {i} {X Y : Ptd i}
  (f : X ⊙→ Y)
  {{_ : has-level 1 (de⊙ X)}} {{_ : has-level 1 (de⊙ Y)}}
  {{_ : is-connected 0 (de⊙ X)}} {{_ : is-connected 0 (de⊙ Y)}}
  (H-X : HSS X) (H-Y : HSS Y) where

  import homotopy.SuspAdjointLoop as SAL
  private
    module Π₂X = Pi2HSusp H-X
    module Π₂Y = Pi2HSusp H-Y

  ⊙decodeN-natural :
    Π₂Y.⊙decodeN ◃⊙∘
    ⊙Trunc-fmap f ◃⊙idf
    =⊙∘
    ⊙Trunc-fmap (⊙Ω-fmap (⊙Susp-fmap (fst f))) ◃⊙∘
    Π₂X.⊙decodeN ◃⊙idf
  ⊙decodeN-natural = =⊙∘-in $
    Π₂Y.⊙decodeN ⊙∘ ⊙Trunc-fmap f
      =⟨ ⊙λ= (⊙Trunc-fmap-⊙∘ (SAL.η Y) f) ⟩
    ⊙Trunc-fmap (SAL.η Y ⊙∘ f)
      =⟨ ap ⊙Trunc-fmap (SAL.η-natural f) ⟩
    ⊙Trunc-fmap (⊙Ω-fmap (⊙Susp-fmap (fst f)) ⊙∘ SAL.η X)
      =⟨ ! (⊙λ= (⊙Trunc-fmap-⊙∘ (⊙Ω-fmap (⊙Susp-fmap (fst f))) (SAL.η X))) ⟩
    ⊙Trunc-fmap (⊙Ω-fmap (⊙Susp-fmap (fst f))) ⊙∘ Π₂X.⊙decodeN =∎

  ⊙encodeN-natural :
    Π₂Y.⊙encodeN ◃⊙∘
    ⊙Trunc-fmap (⊙Ω-fmap (⊙Susp-fmap (fst f))) ◃⊙idf
    =⊙∘
    ⊙Trunc-fmap f ◃⊙∘
    Π₂X.⊙encodeN ◃⊙idf
  ⊙encodeN-natural =
    Π₂Y.⊙encodeN ◃⊙∘
    ⊙Trunc-fmap (⊙Ω-fmap (⊙Susp-fmap (fst f))) ◃⊙idf
      =⊙∘⟨ 2 & 0 & =⊙∘-in {gs = Π₂X.⊙decodeN ◃⊙∘ Π₂X.⊙encodeN ◃⊙idf} $
           ! Π₂X.⊙decodeN-⊙encodeN ⟩
    Π₂Y.⊙encodeN ◃⊙∘
    ⊙Trunc-fmap (⊙Ω-fmap (⊙Susp-fmap (fst f))) ◃⊙∘
    Π₂X.⊙decodeN ◃⊙∘
    Π₂X.⊙encodeN ◃⊙idf
      =⊙∘⟨ 1 & 2 & !⊙∘ ⊙decodeN-natural ⟩
    Π₂Y.⊙encodeN ◃⊙∘
    Π₂Y.⊙decodeN ◃⊙∘
    ⊙Trunc-fmap f ◃⊙∘
    Π₂X.⊙encodeN ◃⊙idf
      =⊙∘⟨ 0 & 2 & =⊙∘-in {gs = ⊙idf-seq} Π₂Y.⊙encodeN-⊙decodeN ⟩
    ⊙Trunc-fmap f ◃⊙∘
    Π₂X.⊙encodeN ◃⊙idf ∎⊙∘
