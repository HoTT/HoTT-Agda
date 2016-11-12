{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.WedgeExtension

module homotopy.Freudenthal where

{- lemma (move this where?) -}
private
  move1-left-on-left : ∀ {i} {A : Type i} {x y : A} (p : x == y) (q : x == y)
    → ((! q) ∙ p == idp → p == q)
  move1-left-on-left p idp h = h

module FreudenthalEquiv
  {i} (n k : ℕ₋₂) (kle : k ≤T S (n +2+ S n))
  (X : Type i) (x₀ : X) (cX : is-connected (S (S n)) X) where

  Q : Susp X → Type i
  Q x = Trunc k (north == x)

  up : X → north' X == north
  up x = merid x ∙ ! (merid x₀)

  Codes-mer-args : WedgeExt.args {a₀ = x₀} {b₀ = [_] {n = k} x₀}
  Codes-mer-args = record {n = n; m = n;
    cA = cX;
    cB = Trunc-preserves-conn k cX;
    P = λ _ _ → (Trunc k X , raise-level-≤T kle Trunc-level);
    f = [_]; g = idf _; p = idp}

  Codes-mer : X → Trunc k X → Trunc k X
  Codes-mer = WedgeExt.ext Codes-mer-args

  Codes-mer-β-l : (λ a → Codes-mer a [ x₀ ]) == [_]
  Codes-mer-β-l = λ= $ WedgeExt.β-l {r = Codes-mer-args}

  Codes-mer-β-r : (λ b → Codes-mer x₀ b) == idf _
  Codes-mer-β-r = λ= $ WedgeExt.β-r {r = Codes-mer-args}

  Codes-mer-coh : app= Codes-mer-β-l x₀ == app= Codes-mer-β-r [ x₀ ]
  Codes-mer-coh =
    app= Codes-mer-β-l x₀
      =⟨ app=-β (WedgeExt.β-l {r = Codes-mer-args}) x₀ ⟩
    WedgeExt.β-l {r = Codes-mer-args} x₀
      =⟨ ! (move1-left-on-left _ _ (WedgeExt.coh {r = Codes-mer-args})) ⟩
    WedgeExt.β-r {r = Codes-mer-args} [ x₀ ]
      =⟨ ! (app=-β (WedgeExt.β-r {r = Codes-mer-args}) [ x₀ ]) ⟩
    app= Codes-mer-β-r [ x₀ ] ∎

  Codes-mer-is-equiv : (x : X) → is-equiv (Codes-mer x)
  Codes-mer-is-equiv =
    conn-elim (pointed-conn-out X x₀ cX)
      (λ x' → (is-equiv (Codes-mer x') , prop-has-level-S is-equiv-is-prop))
      (λ tt → transport is-equiv (! (Codes-mer-β-r)) (snd $ ide _))

  Codes-mer-equiv : (x : X) → Trunc k X ≃ Trunc k X
  Codes-mer-equiv x = (Codes-mer x , Codes-mer-is-equiv x)

  Codes-mer-inv-x₀ : <– (Codes-mer-equiv x₀) == idf _
  Codes-mer-inv-x₀ =
       ap is-equiv.g (conn-elim-β
          (pointed-conn-out X x₀ cX)
          (λ x' → (is-equiv (Codes-mer x') , prop-has-level-S is-equiv-is-prop))
          _ unit)
     ∙ lemma (! (Codes-mer-β-r)) (snd $ ide _)
    where lemma : ∀ {i j} {A : Type i} {B : Type j} {f g : A → B}
            (α : f == g) (e : is-equiv f)
            → is-equiv.g (transport is-equiv α e) == is-equiv.g e
          lemma idp e = idp

  Codes : Susp X → Type i
  Codes = SuspRec.f (Trunc k X) (Trunc k X) (ua ∘ Codes-mer-equiv)

  Codes-has-level : (x : Susp X) → has-level k (Codes x)
  Codes-has-level = Susp-elim Trunc-level Trunc-level
                      (λ _ → prop-has-all-paths-↓ has-level-is-prop)

  decodeN : Codes north → Trunc k (north' X == north)
  decodeN = Trunc-fmap up

  decodeN-pt : decodeN [ x₀ ] == [ idp ]
  decodeN-pt = ap [_] (!-inv-r (merid x₀))

  decodeS : Codes south → Q south
  decodeS = Trunc-fmap merid

  encode₀ : {x : Susp X} → north == x → Codes x
  encode₀ α = transport Codes α [ x₀ ]

  encode : {x : Susp X} → Trunc k (north == x) → Codes x
  encode {x} tα = Trunc-rec (Codes-has-level x) encode₀ tα

  abstract
    encode-decodeN : (c : Codes north) → encode (decodeN c) == c
    encode-decodeN = Trunc-elim
      (λ _ → =-preserves-level _ Trunc-level)
      (λ x →
        encode (decodeN [ x ])
          =⟨ idp ⟩
        coe (ap Codes (merid x ∙ ! (merid x₀))) [ x₀ ]
          =⟨ ap-∙ Codes (merid x) (! (merid x₀)) |in-ctx (λ w → coe w [ x₀ ]) ⟩
        coe (ap Codes (merid x) ∙ ap Codes (! (merid x₀))) [ x₀ ]
          =⟨ coe-∙ (ap Codes (merid x)) (ap Codes (! (merid x₀))) [ x₀ ] ⟩
        coe (ap Codes (! (merid x₀))) (coe (ap Codes (merid x)) [ x₀ ])
          =⟨ SuspRec.merid-β _ _ (ua ∘ Codes-mer-equiv) x
            |in-ctx (λ w → coe (ap Codes (! (merid x₀))) (coe w [ x₀ ])) ⟩
        coe (ap Codes (! (merid x₀))) (coe (ua (Codes-mer-equiv x)) [ x₀ ])
          =⟨ coe-β (Codes-mer-equiv x) [ x₀ ]
            |in-ctx (λ w → coe (ap Codes (! (merid x₀))) w) ⟩
        coe (ap Codes (! (merid x₀))) (Codes-mer x [ x₀ ])
          =⟨ app= Codes-mer-β-l x
            |in-ctx (λ w → coe (ap Codes (! (merid x₀))) w) ⟩
        coe (ap Codes (! (merid x₀))) [ x ]
          =⟨ coe-ap-! Codes (merid x₀) [ x ] ⟩
        coe! (ap Codes (merid x₀)) [ x ]
          =⟨ SuspRec.merid-β _ _ (ua ∘ Codes-mer-equiv) x₀
            |in-ctx (λ w → coe! w [ x ]) ⟩
        coe! (ua (Codes-mer-equiv x₀)) [ x ]
          =⟨ coe!-β (Codes-mer-equiv x₀) [ x ] ⟩
        <– (Codes-mer-equiv x₀) [ x ]
          =⟨ app= Codes-mer-inv-x₀ [ x ] ⟩
        [ x ] ∎)

  decode : {x : Susp X} → Codes x → Q x
  decode {x} = Susp-elim
    {P = λ y → Codes y → Q y}
    decodeN decodeS
    (λ x' → ↓-→-from-transp (λ= (STS x')))
    x
    where
    abstract
      coh : {s₁ s₂ : Susp X} (p : s₁ == s₂)
        → (ap (λ s → s ∙ p) (!-inv-r p))
          == ∙-assoc p (! p) p ∙ ap (λ s → p ∙ s) (!-inv-l p) ∙ ∙-unit-r p
      coh idp = idp

      P : X → X → (S (n +2+ (S n))) -Type (lmax i i)
      P = λ x₁ x₂ →
        ((transport Q (merid x₁) (Trunc-fmap up [ x₂ ])
          == Trunc-fmap (merid) (transport Codes (merid x₁) [ x₂ ])),
         =-preserves-level _ (raise-level-≤T kle Trunc-level))

      f : (a : X) → fst (P a x₀)
      f a =
        transport Q (merid a) [ up x₀ ]
          =⟨ transport-Trunc (north ==_) (merid a) (up x₀) ⟩
        [ transport (north ==_) (merid a) (up x₀) ]
          =⟨ ap [_] $ trans-pathfrom {A = Susp X} (merid a) (up x₀)  ⟩
        [ (merid x₀ ∙ ! (merid x₀)) ∙ merid a ]
          =⟨ ap [_] $ ap (λ s → s ∙ merid a) (!-inv-r (merid x₀)) ⟩
        [ merid a ]
          =⟨ idp ⟩
        Trunc-fmap (merid) [ a ]
          =⟨ ap (Trunc-fmap (merid)) (! (app= Codes-mer-β-l a)) ⟩
        Trunc-fmap (merid) (Codes-mer a [ x₀ ])
          =⟨ ap (Trunc-fmap (merid)) (! (coe-β (Codes-mer-equiv a) [ x₀ ])) ⟩
        Trunc-fmap (merid) (coe (ua (Codes-mer-equiv a)) [ x₀ ])
          =⟨ ! (SuspRec.merid-β _ _ (ua ∘ Codes-mer-equiv) a)
            |in-ctx (λ w → Trunc-fmap (merid) (coe w [ x₀ ])) ⟩
        Trunc-fmap (merid) (transport Codes (merid a) [ x₀ ]) ∎

      g : (b : X) → fst (P x₀ b)
      g b =
        transport Q (merid x₀) [ up b ]
          =⟨ transport-Trunc (north ==_) (merid x₀) (up b) ⟩
        [ transport (north ==_) (merid x₀) (up b) ]
          =⟨ ap [_] $ trans-pathfrom {A = Susp X} (merid x₀) (up b)  ⟩
        [ (merid b ∙ ! (merid x₀)) ∙ merid x₀ ]
          =⟨ ap [_] $ ∙-assoc (merid b) (! (merid x₀)) (merid x₀)
                      ∙ ap (λ s → merid b ∙ s) (!-inv-l (merid x₀))
                      ∙ ∙-unit-r (merid b) ⟩
        [ merid b ]
          =⟨ idp ⟩
        Trunc-fmap (merid) [ b ]
          =⟨ ap (Trunc-fmap (merid)) (! (app= Codes-mer-β-r [ b ])) ⟩
        Trunc-fmap (merid) (Codes-mer x₀ [ b ])
          =⟨ ap (Trunc-fmap (merid)) (! (coe-β (Codes-mer-equiv x₀) [ b ])) ⟩
        Trunc-fmap (merid) (coe (ua (Codes-mer-equiv x₀)) [ b ])
          =⟨ ! (SuspRec.merid-β _ _ (ua ∘ Codes-mer-equiv) x₀)
            |in-ctx (λ w → Trunc-fmap (merid) (coe w [ b ])) ⟩
        Trunc-fmap (merid) (transport Codes (merid x₀) [ b ]) ∎

      p : f x₀ == g x₀
      p = ap2
        (λ p₁ p₂ →
          transport Q (merid x₀) [ up x₀ ]
            =⟨ transport-Trunc (north ==_) (merid x₀) (up x₀) ⟩
          [ transport (north ==_) (merid x₀) (up x₀) ]
            =⟨ ap [_] $ trans-pathfrom {A = Susp X} (merid x₀) (up x₀) ⟩
          [ (merid x₀ ∙ ! (merid x₀)) ∙ merid x₀ ]
            =⟨ ap [_] p₁ ⟩
          [ merid x₀ ]
            =⟨ idp ⟩
          Trunc-fmap (merid) [ x₀ ]
            =⟨ ap (Trunc-fmap (merid)) (! p₂) ⟩
          Trunc-fmap (merid) (Codes-mer x₀ [ x₀ ])
            =⟨ ap (Trunc-fmap (merid)) (! (coe-β (Codes-mer-equiv x₀) [ x₀ ])) ⟩
          Trunc-fmap (merid) (coe (ua (Codes-mer-equiv x₀)) [ x₀ ])
            =⟨ ! (SuspRec.merid-β _ _ (ua ∘ Codes-mer-equiv) x₀)
              |in-ctx (λ w → Trunc-fmap (merid) (coe w [ x₀ ])) ⟩
          Trunc-fmap (merid) (transport Codes (merid x₀) [ x₀ ]) ∎)
        (coh (merid x₀)) Codes-mer-coh

      STS-args : WedgeExt.args {a₀ = x₀} {b₀ = x₀}
      STS-args =
        record {n = n; m = n; cA = cX; cB = cX; P = P; f = f; g = g; p = p}

      STS : (x' : X) (c : Codes north) →
        transport Q (merid x') (Trunc-fmap up c)
        == Trunc-fmap (merid) (transport Codes (merid x') c)
      STS x' = Trunc-elim (λ _ → =-preserves-level _ Trunc-level)
                          (WedgeExt.ext STS-args x')


  decode-encode : {x : Susp X} (tα : Q x)
    → decode {x} (encode {x} tα) == tα
  decode-encode {x} = Trunc-elim
    {P = λ tα → decode {x} (encode {x} tα) == tα}
    (λ _ → =-preserves-level k Trunc-level)
    (J (λ y p → decode {y} (encode {y} [ p ]) == [ p ])
       (ap [_] (!-inv-r (merid x₀))))

  eq : Trunc k X ≃ Trunc k (north' X == north)
  eq = equiv decodeN encode decode-encode encode-decodeN

  ⊙eq : ⊙Trunc k (X , x₀) ⊙≃ ⊙Trunc k (⊙Ω (⊙Susp (X , x₀)))
  ⊙eq = ≃-to-⊙≃ eq (ap [_] (!-inv-r (merid x₀)))

  path : Trunc k X == Trunc k (north' X == north)
  path = ua eq

  ⊙path : ⊙Trunc k (X , x₀) == ⊙Trunc k (⊙Ω (⊙Susp (X , x₀)))
  ⊙path = ⊙ua ⊙eq

{- Used to prove stability in iterated suspensions -}
module FreudenthalIso
  {i} (n : ℕ₋₂) (k : ℕ) (kle : ⟨ S k ⟩ ≤T S (n +2+ S n))
  (X : Ptd i) (cX : is-connected (S (S n)) (fst X)) where

  open FreudenthalEquiv n ⟨ S k ⟩ kle (fst X) (snd X) cX public

  hom : Ω^S-group k (⊙Trunc ⟨ S k ⟩ X) Trunc-level
     →ᴳ Ω^S-group k (⊙Trunc ⟨ S k ⟩ (⊙Ω (⊙Susp X))) Trunc-level
  hom = Ω^S-group-fmap k Trunc-level Trunc-level (decodeN , decodeN-pt)

  iso : Ω^S-group k (⊙Trunc ⟨ S k ⟩ X) Trunc-level
     ≃ᴳ Ω^S-group k (⊙Trunc ⟨ S k ⟩ (⊙Ω (⊙Susp X))) Trunc-level
  iso = Ω^S-group-emap k Trunc-level Trunc-level ⊙eq
