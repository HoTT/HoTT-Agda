{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.WedgeExtension
import homotopy.SuspAdjointLoop as SAL

module homotopy.Freudenthal where

{- lemma (move this where?) -}
private
  move1-left-on-left : ∀ {i} {A : Type i} {x y : A} (p : x == y) (q : x == y)
    → ((! q) ∙ p == idp → p == q)
  move1-left-on-left p idp h = h

module FreudenthalEquiv
  {i} (n k : ℕ₋₂) (kle : k ≤T S n +2+ S n)
  (X : Ptd i) {{cX : is-connected (S (S n)) (de⊙ X)}} where

  Q : Susp (de⊙ X) → Type i
  Q x = Trunc k (north == x)

  ⊙up : X ⊙→ ⊙Ω (⊙Susp (de⊙ X))
  ⊙up = SAL.η _

  up = fst ⊙up

  Codes-mer-args : args {a₀ = pt X} {b₀ = [_] {n = k} (pt X)}
  Codes-mer-args = record {n = S n; m = S n;
    P = λ _ _ → (Trunc k (de⊙ X) , raise-level-≤T kle Trunc-level);
    f = [_]; g = idf _; p = idp}

  module CodesExt =
    WedgeExt {a₀ = pt X} {b₀ = [_] {n = k} (pt X)} Codes-mer-args

  Codes-mer : de⊙ X → Trunc k (de⊙ X) → Trunc k (de⊙ X)
  Codes-mer = CodesExt.ext

  Codes-mer-β-l : (λ a → Codes-mer a [ pt X ]) == [_]
  Codes-mer-β-l = λ= CodesExt.β-l

  Codes-mer-β-r : (λ b → Codes-mer (pt X) b) == idf _
  Codes-mer-β-r = λ= $ CodesExt.β-r

  Codes-mer-coh : app= Codes-mer-β-l (pt X) == app= Codes-mer-β-r [ pt X ]
  Codes-mer-coh =
    app= Codes-mer-β-l (pt X)
      =⟨ app=-β CodesExt.β-l (pt X) ⟩
    CodesExt.β-l (pt X)
      =⟨ ! (move1-left-on-left _ _ CodesExt.coh) ⟩
    CodesExt.β-r [ pt X ]
      =⟨ ! (app=-β CodesExt.β-r [ pt X ]) ⟩
    app= Codes-mer-β-r [ pt X ] ∎

  Codes-mer-is-equiv : (x : de⊙ X) → is-equiv (Codes-mer x)
  Codes-mer-is-equiv =
    conn-extend (pointed-conn-out {n = S n} (de⊙ X) (pt X))
      (λ x' → (is-equiv (Codes-mer x') , is-equiv-level))
      (λ tt → transport is-equiv (! (Codes-mer-β-r)) (idf-is-equiv _))

  Codes-mer-equiv : (x : de⊙ X) → Trunc k (de⊙ X) ≃ Trunc k (de⊙ X)
  Codes-mer-equiv x = (Codes-mer x , Codes-mer-is-equiv x)

  Codes-mer-inv-x₀ : <– (Codes-mer-equiv (pt X)) == idf _
  Codes-mer-inv-x₀ =
       ap is-equiv.g (conn-extend-β
          (pointed-conn-out (de⊙ X) (pt X))
          (λ x' → (is-equiv (Codes-mer x') , is-equiv-level))
          _ unit)
     ∙ lemma (! (Codes-mer-β-r)) (snd $ ide _)
    where lemma : ∀ {i j} {A : Type i} {B : Type j} {f g : A → B}
            (α : f == g) (e : is-equiv f)
            → is-equiv.g (transport is-equiv α e) == is-equiv.g e
          lemma idp e = idp

  module CodesRec = SuspRec (Trunc k (de⊙ X)) (Trunc k (de⊙ X)) (ua ∘ Codes-mer-equiv)

  Codes : Susp (de⊙ X) → Type i
  Codes = CodesRec.f

  Codes-has-level : (x : Susp (de⊙ X)) → has-level k (Codes x)
  Codes-has-level = Susp-elim Trunc-level Trunc-level
                      (λ _ → prop-has-all-paths-↓)

  {-
    favonia:

    This equation should be true: [⊙Trunc-fmap ⊙up = (decodeN , decodeN-pt)].
    Maybe there is a way to refactor the following code so that
    pointedness is handled more elegantly.
  -}

  decodeN : Codes north → Trunc k (north' (de⊙ X) == north)
  decodeN = Trunc-fmap up

  decodeN-pt : decodeN [ pt X ] == [ idp ]
  decodeN-pt = snd (⊙Trunc-fmap ⊙up)

  decodeS : Codes south → Q south
  decodeS = Trunc-fmap merid

  encode₀ : {x : Susp (de⊙ X)} → north == x → Codes x
  encode₀ α = transport Codes α [ pt X ]

  encode : {x : Susp (de⊙ X)} → Trunc k (north == x) → Codes x
  encode {x} tα = Trunc-rec {{Codes-has-level x}} encode₀ tα

  ⊙decodeN : ⊙Trunc k X ⊙→ ⊙Trunc k (⊙Ω (⊙Susp (de⊙ X)))
  ⊙decodeN = decodeN , ap [_] (!-inv-r (merid (pt X)))

  ⊙encodeN : ⊙Trunc k (⊙Ω (⊙Susp (de⊙ X))) ⊙→ ⊙Trunc k X
  ⊙encodeN = encode , idp

  abstract
    encode-decodeN : (c : Codes north) → encode (decodeN c) == c
    encode-decodeN = Trunc-elim
      {{λ _ → =-preserves-level Trunc-level}}
      (λ x →
        encode (decodeN [ x ])
          =⟨ idp ⟩
        coe (ap Codes (merid x ∙ ! (merid (pt X)))) [ pt X ]
          =⟨ ap-∙ Codes (merid x) (! (merid (pt X))) |in-ctx (λ w → coe w [ pt X ]) ⟩
        coe (ap Codes (merid x) ∙ ap Codes (! (merid (pt X)))) [ pt X ]
          =⟨ coe-∙ (ap Codes (merid x)) (ap Codes (! (merid (pt X)))) [ pt X ] ⟩
        coe (ap Codes (! (merid (pt X)))) (coe (ap Codes (merid x)) [ pt X ])
          =⟨ SuspRec.merid-β _ _ (ua ∘ Codes-mer-equiv) x
            |in-ctx (λ w → coe (ap Codes (! (merid (pt X)))) (coe w [ pt X ])) ⟩
        coe (ap Codes (! (merid (pt X)))) (coe (ua (Codes-mer-equiv x)) [ pt X ])
          =⟨ coe-β (Codes-mer-equiv x) [ pt X ]
            |in-ctx (λ w → coe (ap Codes (! (merid (pt X)))) w) ⟩
        coe (ap Codes (! (merid (pt X)))) (Codes-mer x [ pt X ])
          =⟨ app= Codes-mer-β-l x
            |in-ctx (λ w → coe (ap Codes (! (merid (pt X)))) w) ⟩
        coe (ap Codes (! (merid (pt X)))) [ x ]
          =⟨ coe-ap-! Codes (merid (pt X)) [ x ] ⟩
        coe! (ap Codes (merid (pt X))) [ x ]
          =⟨ SuspRec.merid-β _ _ (ua ∘ Codes-mer-equiv) (pt X)
            |in-ctx (λ w → coe! w [ x ]) ⟩
        coe! (ua (Codes-mer-equiv (pt X))) [ x ]
          =⟨ coe!-β (Codes-mer-equiv (pt X)) [ x ] ⟩
        <– (Codes-mer-equiv (pt X)) [ x ]
          =⟨ app= Codes-mer-inv-x₀ [ x ] ⟩
        [ x ] ∎)

  decode : {x : Susp (de⊙ X)} → Codes x → Q x
  decode {x} = Susp-elim
    {P = λ y → Codes y → Q y}
    decodeN decodeS
    (λ x' → ↓-→-from-transp (λ= (STS x')))
    x
    where
    abstract
      coh : {s₁ s₂ : Susp (de⊙ X)} (p : s₁ == s₂)
        → (ap (λ s → s ∙ p) (!-inv-r p))
          == ∙-assoc p (! p) p ∙ ap (λ s → p ∙ s) (!-inv-l p) ∙ ∙-unit-r p
      coh idp = idp

      P : de⊙ X → de⊙ X → (S (n +2+ (S n))) -Type (lmax i i)
      P = λ x₁ x₂ →
        ((transport Q (merid x₁) (Trunc-fmap up [ x₂ ])
          == Trunc-fmap merid (transport Codes (merid x₁) [ x₂ ])),
         =-preserves-level (raise-level-≤T kle Trunc-level))

      f : (a : de⊙ X) → fst (P a (pt X))
      f a =
        transport Q (merid a) [ up (pt X) ]
          =⟨ transport-Trunc' (north ==_) (merid a) (up (pt X)) ⟩
        [ transport (north ==_) (merid a) (up (pt X)) ]
          =⟨ ap [_] $ transp-cst=idf {A = Susp (de⊙ X)} (merid a) (up (pt X)) ⟩
        [ (merid (pt X) ∙ ! (merid (pt X))) ∙ merid a ]
          =⟨ ap [_] $ ap (λ s → s ∙ merid a) (!-inv-r (merid (pt X))) ⟩
        [ merid a ]
          =⟨ idp ⟩
        Trunc-fmap merid [ a ]
          =⟨ ap (Trunc-fmap merid) (! (app= Codes-mer-β-l a)) ⟩
        Trunc-fmap merid (Codes-mer a [ pt X ])
          =⟨ ap (Trunc-fmap merid) (! (coe-β (Codes-mer-equiv a) [ pt X ])) ⟩
        Trunc-fmap merid (coe (ua (Codes-mer-equiv a)) [ pt X ])
          =⟨ ! (SuspRec.merid-β _ _ (ua ∘ Codes-mer-equiv) a)
            |in-ctx (λ w → Trunc-fmap merid (coe w [ pt X ])) ⟩
        Trunc-fmap merid (transport Codes (merid a) [ pt X ]) ∎

      g : (b : de⊙ X) → fst (P (pt X) b)
      g b =
        transport Q (merid (pt X)) [ up b ]
          =⟨ transport-Trunc' (north ==_) (merid (pt X)) (up b) ⟩
        [ transport (north ==_) (merid (pt X)) (up b) ]
          =⟨ ap [_] $ transp-cst=idf {A = Susp (de⊙ X)} (merid (pt X)) (up b)  ⟩
        [ (merid b ∙ ! (merid (pt X))) ∙ merid (pt X) ]
          =⟨ ap [_] $ ∙-assoc (merid b) (! (merid (pt X))) (merid (pt X))
                      ∙ ap (λ s → merid b ∙ s) (!-inv-l (merid (pt X)))
                      ∙ ∙-unit-r (merid b) ⟩
        [ merid b ]
          =⟨ idp ⟩
        Trunc-fmap merid [ b ]
          =⟨ ap (Trunc-fmap merid) (! (app= Codes-mer-β-r [ b ])) ⟩
        Trunc-fmap merid (Codes-mer (pt X) [ b ])
          =⟨ ap (Trunc-fmap merid) (! (coe-β (Codes-mer-equiv (pt X)) [ b ])) ⟩
        Trunc-fmap merid (coe (ua (Codes-mer-equiv (pt X))) [ b ])
          =⟨ ! (SuspRec.merid-β _ _ (ua ∘ Codes-mer-equiv) (pt X))
            |in-ctx (λ w → Trunc-fmap merid (coe w [ b ])) ⟩
        Trunc-fmap merid (transport Codes (merid (pt X)) [ b ]) ∎

      p : f (pt X) == g (pt X)
      p = ap2
        (λ p₁ p₂ →
          transport Q (merid (pt X)) [ up (pt X) ]
            =⟨ transport-Trunc' (north ==_) (merid (pt X)) (up (pt X)) ⟩
          [ transport (north ==_) (merid (pt X)) (up (pt X)) ]
            =⟨ ap [_] $ transp-cst=idf {A = Susp (de⊙ X)} (merid (pt X)) (up (pt X)) ⟩
          [ (merid (pt X) ∙ ! (merid (pt X))) ∙ merid (pt X) ]
            =⟨ ap [_] p₁ ⟩
          [ merid (pt X) ]
            =⟨ idp ⟩
          Trunc-fmap merid [ pt X ]
            =⟨ ap (Trunc-fmap merid) (! p₂) ⟩
          Trunc-fmap merid (Codes-mer (pt X) [ pt X ])
            =⟨ ap (Trunc-fmap merid) (! (coe-β (Codes-mer-equiv (pt X)) [ pt X ])) ⟩
          Trunc-fmap merid (coe (ua (Codes-mer-equiv (pt X))) [ pt X ])
            =⟨ ! (SuspRec.merid-β _ _ (ua ∘ Codes-mer-equiv) (pt X))
              |in-ctx (λ w → Trunc-fmap merid (coe w [ pt X ])) ⟩
          Trunc-fmap merid (transport Codes (merid (pt X)) [ pt X ]) ∎)
        (coh (merid (pt X))) Codes-mer-coh

      STS-args : args {a₀ = pt X} {b₀ = pt X}
      STS-args =
        record {n = S n; m = S n; P = P; f = f; g = g; p = p}

      STS : (x' : de⊙ X) (c : Codes north) →
        transport Q (merid x') (Trunc-fmap up c)
        == Trunc-fmap merid (transport Codes (merid x') c)
      STS x' = Trunc-elim {{λ _ → =-preserves-level Trunc-level}}
                          (WedgeExt.ext STS-args x')

  abstract
    decode-encode : {x : Susp (de⊙ X)} (tα : Q x)
      → decode {x} (encode {x} tα) == tα
    decode-encode {x} = Trunc-elim
      {P = λ tα → decode {x} (encode {x} tα) == tα}
      {{λ _ → =-preserves-level Trunc-level}}
      (J (λ y p → decode {y} (encode {y} [ p ]) == [ p ])
         (ap [_] (!-inv-r (merid (pt X)))))

  eq : Trunc k (de⊙ X) ≃ Trunc k (north' (de⊙ X) == north)
  eq = equiv decodeN encode decode-encode encode-decodeN

  ⊙eq : ⊙Trunc k X ⊙≃ ⊙Trunc k (⊙Ω (⊙Susp (de⊙ X)))
  ⊙eq = ≃-to-⊙≃ eq (snd ⊙decodeN)

  abstract
    ⊙decodeN-⊙encodeN : ⊙decodeN ⊙∘ ⊙encodeN == ⊙idf _
    ⊙decodeN-⊙encodeN =
      ⊙λ=' {X = ⊙Trunc k (⊙Ω (⊙Susp (de⊙ X)))}
           {Y = ⊙Trunc k (⊙Ω (⊙Susp (de⊙ X)))}
           decode-encode $
      ↓-idf=cst-in $
      ! (∙-unit-r (ap [_] (!-inv-r (merid (pt X)))))

    ⊙<–-⊙eq : ⊙<– ⊙eq == ⊙encodeN
    ⊙<–-⊙eq =
      –>-is-inj (post⊙∘-equiv {Z = ⊙Trunc k (⊙Ω (⊙Susp (de⊙ X)))} ⊙eq) (⊙<– ⊙eq) ⊙encodeN $
      ⊙decodeN ⊙∘ ⊙<– ⊙eq
        =⟨ ⊙<–-inv-r ⊙eq ⟩
      ⊙idf _
        =⟨ ! ⊙decodeN-⊙encodeN ⟩
      ⊙decodeN ⊙∘ ⊙encodeN =∎

  path : Trunc k (de⊙ X) == Trunc k (north' (de⊙ X) == north)
  path = ua eq

  ⊙path : ⊙Trunc k X == ⊙Trunc k (⊙Ω (⊙Susp (de⊙ X)))
  ⊙path = ⊙ua ⊙eq

{- timjb: it is probably easier to show the naturality of ⊙decodeN
   and deduce the naturality of ⊙encodeN from that than to show
   the naturality of ⊙encodeN directly (as done below) -}
module FreudenthalEquivNatural
  {i} (n k : ℕ₋₂) (kle : k ≤T S n +2+ S n)
  {X Y : Ptd i} (f : X ⊙→ Y)
  {{cX : is-connected (S (S n)) (de⊙ X)}}
  {{cY : is-connected (S (S n)) (de⊙ Y)}} where

  private
    module FX = FreudenthalEquiv n k kle X {{cX}}
    module FY = FreudenthalEquiv n k kle Y {{cY}}

  Codes-mer-map : ∀ (x : de⊙ X) (tx : Trunc k (de⊙ X))
    → Trunc-fmap (fst f) (FX.Codes-mer x tx) ==
      FY.Codes-mer (fst f x) (Trunc-fmap (fst f) tx)
  Codes-mer-map =
    WedgeExt.ext {A = de⊙ X} {a₀ = pt X} {B = Trunc k (de⊙ X)} {b₀ = [ pt X ]} $
    record
    { n = S n; m = S n
    ; P = λ x tx → (P x tx , P-level x tx)
    ; f = λ x → ↯ (f-seq x)
    ; g = λ tx → ↯ (g-seq tx)
    ; p = =ₛ-out p
    }
    where
    P : de⊙ X → Trunc k (de⊙ X) → Type i
    P x tx =
      Trunc-fmap (fst f) (FX.Codes-mer x tx) ==
      FY.Codes-mer (fst f x) (Trunc-fmap (fst f) tx)
    P-level : ∀ x tx → has-level (S n +2+ S n) (P x tx)
    P-level x tx = =-preserves-level (raise-level-≤T kle Trunc-level)
    f-seq : ∀ x → Trunc-fmap (fst f) (FX.Codes-mer x [ pt X ]) =-=
                  FY.Codes-mer (fst f x) (Trunc-fmap (fst f) [ pt X ])
    f-seq x =
      Trunc-fmap (fst f) (FX.Codes-mer x [ pt X ])
        =⟪ ap (Trunc-fmap (fst f)) (FX.CodesExt.β-l x) ⟫
      [ fst f x ]
        =⟪ ! (FY.CodesExt.β-l (fst f x)) ⟫
      FY.Codes-mer (fst f x) [ pt Y ]
        =⟪ ap (FY.Codes-mer (fst f x) ∘ [_]) (! (snd f)) ⟫
      FY.Codes-mer (fst f x) [ fst f (pt X) ] ∎∎
    g-seq : ∀ tx → Trunc-fmap (fst f) (FX.Codes-mer (pt X) tx) =-=
                   FY.Codes-mer (fst f (pt X)) (Trunc-fmap (fst f) tx)
    g-seq tx =
      Trunc-fmap (fst f) (FX.Codes-mer (pt X) tx)
        =⟪ ap (Trunc-fmap (fst f)) (FX.CodesExt.β-r tx) ⟫
      Trunc-fmap (fst f) tx
        =⟪ ! (FY.CodesExt.β-r (Trunc-fmap (fst f) tx)) ⟫
      FY.Codes-mer (pt Y) (Trunc-fmap (fst f) tx)
        =⟪ ap (λ y → FY.Codes-mer y (Trunc-fmap (fst f) tx)) (! (snd f)) ⟫
      FY.Codes-mer (fst f (pt X)) (Trunc-fmap (fst f) tx) ∎∎
    p : f-seq (pt X) =ₛ g-seq [ pt X ]
    p =
      ap (Trunc-fmap (fst f)) (FX.CodesExt.β-l (pt X)) ◃∙
      ! (FY.CodesExt.β-l (fst f (pt X))) ◃∙
      ap (FY.Codes-mer (fst f (pt X)) ∘ [_]) (! (snd f)) ◃∎
        =ₛ⟨ 0 & 1 & ap-seq-=ₛ (Trunc-fmap (fst f)) $
                    pre-rotate-out {p = FX.CodesExt.β-l (pt X)} {q = []} {r = FX.CodesExt.β-r [ pt X ] ◃∎} $
                    =ₛ-in $ ! $ FX.CodesExt.coh ⟩
      ap (Trunc-fmap (fst f)) (FX.CodesExt.β-r [ pt X ]) ◃∙
      ! (FY.CodesExt.β-l (fst f (pt X))) ◃∙
      ap (FY.Codes-mer (fst f (pt X)) ∘ [_]) (! (snd f)) ◃∎
        =ₛ⟨ 1 & 1 & pre-rotate-in $
            homotopy-naturality
              [_]
              (λ y → FY.Codes-mer y [ pt Y ])
              (! ∘ FY.CodesExt.β-l)
              (! (snd f)) ⟩
      ap (Trunc-fmap (fst f)) (FX.CodesExt.β-r [ pt X ]) ◃∙
      ! (ap [_] (! (snd f))) ◃∙
      ! (FY.CodesExt.β-l (pt Y)) ◃∙
      ap (λ y → FY.Codes-mer y [ pt Y ]) (! (snd f)) ◃∙
      ap (FY.Codes-mer (fst f (pt X)) ∘ [_]) (! (snd f)) ◃∎
        =ₛ⟨ 3 & 2 & ap-comm-=ₛ (λ y y' → FY.Codes-mer y [ y' ]) (! (snd f)) (! (snd f)) ⟩
      ap (Trunc-fmap (fst f)) (FX.CodesExt.β-r [ pt X ]) ◃∙
      ! (ap [_] (! (snd f))) ◃∙
      ! (FY.CodesExt.β-l (pt Y)) ◃∙
      ap (λ y → FY.Codes-mer (pt Y) [ y ]) (! (snd f)) ◃∙
      ap (λ y → FY.Codes-mer y [ fst f (pt X) ]) (! (snd f)) ◃∎
        =ₛ⟨ 2 & 1 & !-=ₛ $
            pre-rotate-out {p = FY.CodesExt.β-l (pt Y)} {q = []} {r = FY.CodesExt.β-r [ pt Y ] ◃∎} $
            =ₛ-in $ ! $ FY.CodesExt.coh ⟩
      ap (Trunc-fmap (fst f)) (FX.CodesExt.β-r [ pt X ]) ◃∙
      ! (ap [_] (! (snd f))) ◃∙
      ! (FY.CodesExt.β-r [ pt Y ]) ◃∙
      ap (λ y → FY.Codes-mer (pt Y) [ y ]) (! (snd f)) ◃∙
      ap (λ y → FY.Codes-mer y [ fst f (pt X) ]) (! (snd f)) ◃∎
        =ₛ⟨ 1 & 3 & !ₛ $ pre-rotate-in $
            homotopy-naturality
              [_]
              (FY.Codes-mer (pt Y) ∘ [_])
              (! ∘ FY.CodesExt.β-r ∘ [_])
              (! (snd f)) ⟩
      ap (Trunc-fmap (fst f)) (FX.CodesExt.β-r [ pt X ]) ◃∙
      ! (FY.CodesExt.β-r (Trunc-fmap (fst f) [ pt X ])) ◃∙
      ap (λ y → FY.Codes-mer y [ fst f (pt X) ]) (! (snd f)) ◃∎ ∎ₛ

  Codes-fmap : ∀ {x : Susp (de⊙ X)}
    → FX.Codes x
    → FY.Codes (Susp-fmap (fst f) x)
  Codes-fmap {x} =
    Susp-elim
      {P = λ x → FX.Codes x → FY.Codes (Susp-fmap (fst f) x)}
      (Trunc-fmap (fst f))
      (Trunc-fmap (fst f))
      (λ x → ↓-→-from-transp $ λ= $
        Trunc-elim {{λ tx → =-preserves-level Trunc-level}} $ λ x' →
        transport (FY.Codes ∘ Susp-fmap (fst f)) (merid x) [ fst f x' ]
          =⟨ ap (λ q → coe q [ fst f x' ]) (ap-∘ FY.Codes (Susp-fmap (fst f)) (merid x)) ⟩
        transport FY.Codes (ap (Susp-fmap (fst f)) (merid x)) [ fst f x' ]
          =⟨ ap (λ p → transport FY.Codes p [ fst f x' ]) $
             SuspFmap.merid-β (fst f) x ⟩
        transport FY.Codes (merid (fst f x)) [ fst f x' ]
          =⟨ ap (λ p → coe p [ fst f x' ]) (FY.CodesRec.merid-β (fst f x)) ⟩
        coe (ua (FY.Codes-mer-equiv (fst f x))) [ fst f x' ]
          =⟨ coe-β (FY.Codes-mer-equiv (fst f x)) [ fst f x' ] ⟩
        FY.Codes-mer (fst f x) [ fst f x' ]
          =⟨ ! (Codes-mer-map x [ x' ])  ⟩
        Trunc-fmap (fst f) (FX.Codes-mer x [ x' ])
          =⟨ ap (Trunc-fmap (fst f)) (! (coe-β (FX.Codes-mer-equiv x) [ x' ])) ⟩
        Trunc-fmap (fst f) (coe (ua (FX.Codes-mer-equiv x)) [ x' ])
          =⟨ ap (λ p → Trunc-fmap (fst f) (coe p [ x' ])) (! (FX.CodesRec.merid-β x)) ⟩
        Trunc-fmap (fst f) (transport FX.Codes (merid x) [ x' ]) =∎)
      x

  encode-natural : ∀ {x : Susp (de⊙ X)}
    (tα : Trunc k (north == x))
    → FY.encode (Trunc-fmap (ap (Susp-fmap (fst f))) tα)
      ==
      Codes-fmap {x} (FX.encode tα)
  encode-natural {x} =
    Trunc-elim {{λ tα → =-preserves-level (FY.Codes-has-level (Susp-fmap (fst f) x))}} $
    J (λ x p → FY.encode (Trunc-fmap (ap (Susp-fmap (fst f))) [ p ]) == Codes-fmap {x} (FX.encode [ p ])) $
    ! (ap [_] (snd f))

  ⊙encodeN-natural :
    FY.⊙encodeN ◃⊙∘
    ⊙Trunc-fmap (⊙Ω-fmap (⊙Susp-fmap (fst f))) ◃⊙idf
    =⊙∘
    ⊙Trunc-fmap f ◃⊙∘
    FX.⊙encodeN ◃⊙idf
  ⊙encodeN-natural =
    =⊙∘-in $
    ⊙λ=' {X = ⊙Trunc k (⊙Ω (⊙Susp (de⊙ X)))} {Y = ⊙Trunc k Y} (encode-natural {north}) $
    ↓-idf=cst-in {p = ! (ap [_] (snd f))} $
    ! $ !-inv-l (ap [_] (snd f))

{- Used to prove stability in iterated suspensions -}
module FreudenthalIso
  {i} (n : ℕ₋₂) (k : ℕ) (kle : ⟨ S k ⟩ ≤T S n +2+ S n)
  (X : Ptd i) {{_ : is-connected (S (S n)) (de⊙ X)}} where

  open FreudenthalEquiv n ⟨ S k ⟩ kle X public

  hom : Ω^S-group k (⊙Trunc ⟨ S k ⟩ X)
     →ᴳ Ω^S-group k (⊙Trunc ⟨ S k ⟩ (⊙Ω (⊙Susp (de⊙ X))))
  hom = Ω^S-group-fmap k (decodeN , decodeN-pt)

  iso : Ω^S-group k (⊙Trunc ⟨ S k ⟩ X)
     ≃ᴳ Ω^S-group k (⊙Trunc ⟨ S k ⟩ (⊙Ω (⊙Susp (de⊙ X))))
  iso = Ω^S-group-emap k ⊙eq
