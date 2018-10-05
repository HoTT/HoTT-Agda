{-# OPTIONS --without-K --rewriting #-}

open import HoTT
import homotopy.WedgeExtension as WedgeExt
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

  Codes-mer-args : WedgeExt.args {a₀ = pt X} {b₀ = [_] {n = k} (pt X)}
  Codes-mer-args = record {n = S n; m = S n;
    P = λ _ _ → (Trunc k (de⊙ X) , raise-level-≤T kle Trunc-level);
    f = [_]; g = idf _; p = idp}

  Codes-mer : de⊙ X → Trunc k (de⊙ X) → Trunc k (de⊙ X)
  Codes-mer = WedgeExt.ext Codes-mer-args

  Codes-mer-β-l : (λ a → Codes-mer a [ pt X ]) == [_]
  Codes-mer-β-l = λ= $ WedgeExt.β-l {r = Codes-mer-args}

  Codes-mer-β-r : (λ b → Codes-mer (pt X) b) == idf _
  Codes-mer-β-r = λ= $ WedgeExt.β-r {r = Codes-mer-args}

  Codes-mer-coh : app= Codes-mer-β-l (pt X) == app= Codes-mer-β-r [ pt X ]
  Codes-mer-coh =
    app= Codes-mer-β-l (pt X)
      =⟨ app=-β (WedgeExt.β-l {r = Codes-mer-args}) (pt X) ⟩
    WedgeExt.β-l {r = Codes-mer-args} (pt X)
      =⟨ ! (move1-left-on-left _ _ (WedgeExt.coh {r = Codes-mer-args})) ⟩
    WedgeExt.β-r {r = Codes-mer-args} [ pt X ]
      =⟨ ! (app=-β (WedgeExt.β-r {r = Codes-mer-args}) [ pt X ]) ⟩
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

  Codes : Susp (de⊙ X) → Type i
  Codes = SuspRec.f (Trunc k (de⊙ X)) (Trunc k (de⊙ X)) (ua ∘ Codes-mer-equiv)

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
          =⟨ transport-Trunc (north ==_) (merid a) (up (pt X)) ⟩
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
          =⟨ transport-Trunc (north ==_) (merid (pt X)) (up b) ⟩
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
            =⟨ transport-Trunc (north ==_) (merid (pt X)) (up (pt X)) ⟩
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

      STS-args : WedgeExt.args {a₀ = pt X} {b₀ = pt X}
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
  ⊙eq = ≃-to-⊙≃ eq (ap [_] (!-inv-r (merid (pt X))))

  path : Trunc k (de⊙ X) == Trunc k (north' (de⊙ X) == north)
  path = ua eq

  ⊙path : ⊙Trunc k X == ⊙Trunc k (⊙Ω (⊙Susp (de⊙ X)))
  ⊙path = ⊙ua ⊙eq

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
