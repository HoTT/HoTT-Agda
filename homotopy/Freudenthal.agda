{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.Equivalences2
open import lib.NType2
open import lib.NConnected
open import lib.types.TLevel
open import lib.types.Truncation
open import lib.types.Suspension
open import homotopy.WedgeExtension

module homotopy.Freudenthal where

{- some lemmas (move these?) -}
private
  ap2 : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} {x y : A} {w z : B} 
    (f : A → B → C) → (x == y) → (w == z) 
    → f x w == f y z
  ap2 f idp idp = idp

  move1-left-on-left : ∀ {i} {A : Type i} {x y : A} (p : x == y) (q : x == y)
    → ((! q) ∙ p == idp → p == q)
  move1-left-on-left p idp h = h

module FreudenthalEquiv
  {i} (n k : ℕ₋₂) (kle : k ≤T S (n +2+ S n))
  (X : Type i) (x₀ : X) (cX : is-connected (S (S n)) X) where

  P : Suspension X → Type i
  P x = Trunc k (north X == x)

  up : X → north X == north X
  up x = merid X x ∙ ! (merid X x₀)

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
      app=-β _ x₀ 
    ∙ ! (move1-left-on-left _ _ (WedgeExt.coh {r = Codes-mer-args}))
    ∙ ! (app=-β _ [ x₀ ])

  Codes-mer-is-equiv : (x : X) → is-equiv (Codes-mer x)
  Codes-mer-is-equiv =
    conn-elim (pointed-conn-out X x₀ cX)
      (λ x' → (is-equiv (Codes-mer x') , 
               prop-has-level-S (is-equiv-is-prop (Codes-mer x'))))
      (λ tt → transport is-equiv (! (Codes-mer-β-r)) (snd $ ide _))

  Codes-mer-equiv : (x : X) → Trunc k X ≃ Trunc k X
  Codes-mer-equiv x = (Codes-mer x , Codes-mer-is-equiv x)

  Codes-mer-inv-x₀ : <– (Codes-mer-equiv x₀) == idf _
  Codes-mer-inv-x₀ = 
       ap is-equiv.g (conn-elim-β _ _ _ unit) 
     ∙ lemma (! (Codes-mer-β-r)) (snd $ ide _)
    where lemma : ∀ {i j} {A : Type i} {B : Type j} {f g : A → B} 
            (α : f == g) (e : is-equiv f)
            → is-equiv.g (transport is-equiv α e) == is-equiv.g e
          lemma idp e = idp

  Codes : Suspension X → Type i
  Codes = SuspensionRec.f X (Trunc k X) (Trunc k X) (ua ∘ Codes-mer-equiv)

  Codes-has-level : (x : Suspension X) → has-level k (Codes x)
  Codes-has-level = Suspension-elim X Trunc-level Trunc-level 
                      (λ _ → prop-has-all-paths-↓ has-level-is-prop)

  decodeN : Codes (north X) → Trunc k (north X == north X)
  decodeN = Trunc-fmap up

  decodeS : Codes (south X) → P (south X)
  decodeS = Trunc-fmap (merid X)

  encode₀ : {x : Suspension X} → north X == x → Codes x
  encode₀ α = transport Codes α [ x₀ ]

  encode : {x : Suspension X} → Trunc k (north X == x) → Codes x
  encode {x} tα = Trunc-rec (Codes-has-level x) encode₀ tα

  abstract
    encode-decodeN : (c : Codes (north X)) → encode (decodeN c) == c
    encode-decodeN = Trunc-elim
      (λ _ → =-preserves-level _ Trunc-level)
      (λ x → 
        encode (decodeN [ x ])
          =⟨ idp ⟩
        coe (ap Codes (merid X x ∙ ! (merid X x₀))) [ x₀ ]
          =⟨ ap-∙ Codes (merid X x) (! (merid X x₀)) |in-ctx (λ w → coe w [ x₀ ]) ⟩
        coe (ap Codes (merid X x) ∙ ap Codes (! (merid X x₀))) [ x₀ ]
          =⟨ coe-∙ (ap Codes (merid X x)) (ap Codes (! (merid X x₀))) [ x₀ ] ⟩
        coe (ap Codes (! (merid X x₀))) (coe (ap Codes (merid X x)) [ x₀ ])
          =⟨ SuspensionRec.glue-β X _ _ (ua ∘ Codes-mer-equiv) x
            |in-ctx (λ w → coe (ap Codes (! (merid X x₀))) (coe w [ x₀ ])) ⟩
        coe (ap Codes (! (merid X x₀))) (coe (ua (Codes-mer-equiv x)) [ x₀ ])
          =⟨ coe-β (Codes-mer-equiv x) [ x₀ ]
            |in-ctx (λ w → coe (ap Codes (! (merid X x₀))) w) ⟩
        coe (ap Codes (! (merid X x₀))) (Codes-mer x [ x₀ ])
          =⟨ app= Codes-mer-β-l x 
            |in-ctx (λ w → coe (ap Codes (! (merid X x₀))) w) ⟩
        coe (ap Codes (! (merid X x₀))) [ x ]
          =⟨ coe-ap-! Codes (merid X x₀) [ x ] ⟩
        coe! (ap Codes (merid X x₀)) [ x ]
          =⟨ SuspensionRec.glue-β X _ _ (ua ∘ Codes-mer-equiv) x₀
            |in-ctx (λ w → coe! w [ x ]) ⟩
        coe! (ua (Codes-mer-equiv x₀)) [ x ]
          =⟨ coe!-β (Codes-mer-equiv x₀) [ x ] ⟩
        <– (Codes-mer-equiv x₀) [ x ]
          =⟨ app= Codes-mer-inv-x₀ [ x ] ⟩
        [ x ] ∎)

  decode : {x : Suspension X} → Codes x → P x
  decode {x} = Suspension-elim X 
    {P = λ y → Codes y → P y}
    decodeN decodeS
    (λ x' → coe (↓-→-is-square {B = Codes} {C = P} 
                   decodeN decodeS (merid X x')) (λ= (STS x')))
    x

    where
    abstract
      STS-args : WedgeExt.args {a₀ = x₀} {b₀ = x₀}
      STS-args = record {n = n; m = n; cA = cX; cB = cX;
        P = λ x₁ x₂ → 
          ((transport P (merid X x₁) (Trunc-fmap up [ x₂ ])
            == Trunc-fmap (merid X) (transport Codes (merid X x₁) [ x₂ ])),
           =-preserves-level _ (raise-level-≤T kle Trunc-level));

        f = λ a → 
          transport P (merid X a) [ up x₀ ]
            =⟨ transport-Trunc (λ y → north X == y) (merid X a) (up x₀) ⟩
          [ transport (λ y → north X == y) (merid X a) (up x₀) ]
            =⟨ ap [_] $ trans-pathfrom {A = Suspension X} (merid X a) (up x₀)  ⟩
          [ (merid X x₀ ∙ ! (merid X x₀)) ∙ merid X a ]
            =⟨ ap [_] $ ap (λ s → s ∙ merid X a) (!-inv-r (merid X x₀)) ⟩
          [ merid X a ]
            =⟨ idp ⟩
          Trunc-fmap (merid X) [ a ]
            =⟨ ap (Trunc-fmap (merid X)) (! (app= Codes-mer-β-l a)) ⟩
          Trunc-fmap (merid X) (Codes-mer a [ x₀ ])
            =⟨ ap (Trunc-fmap (merid X)) (! (coe-β (Codes-mer-equiv a) [ x₀ ])) ⟩
          Trunc-fmap (merid X) (coe (ua (Codes-mer-equiv a)) [ x₀ ])
            =⟨ ! (SuspensionRec.glue-β X _ _ (ua ∘ Codes-mer-equiv) a)
              |in-ctx (λ w → Trunc-fmap (merid X) (coe w [ x₀ ])) ⟩
          Trunc-fmap (merid X) (transport Codes (merid X a) [ x₀ ]) ∎;

        g = λ b → 
          transport P (merid X x₀) [ up b ]
            =⟨ transport-Trunc (λ y → north X == y) (merid X x₀) (up b) ⟩
          [ transport (λ y → north X == y) (merid X x₀) (up b) ]
            =⟨ ap [_] $ trans-pathfrom {A = Suspension X} (merid X x₀) (up b)  ⟩
          [ (merid X b ∙ ! (merid X x₀)) ∙ merid X x₀ ]
            =⟨ ap [_] $ ∙-assoc (merid X b) (! (merid X x₀)) (merid X x₀)
                        ∙ ap (λ s → merid X b ∙ s) (!-inv-l (merid X x₀))
                        ∙ ∙-unit-r (merid X b) ⟩
          [ merid X b ]
            =⟨ idp ⟩
          Trunc-fmap (merid X) [ b ]
            =⟨ ap (Trunc-fmap (merid X)) (! (app= Codes-mer-β-r [ b ])) ⟩
          Trunc-fmap (merid X) (Codes-mer x₀ [ b ])
            =⟨ ap (Trunc-fmap (merid X)) (! (coe-β (Codes-mer-equiv x₀) [ b ])) ⟩
          Trunc-fmap (merid X) (coe (ua (Codes-mer-equiv x₀)) [ b ])
            =⟨ ! (SuspensionRec.glue-β X _ _ (ua ∘ Codes-mer-equiv) x₀)
              |in-ctx (λ w → Trunc-fmap (merid X) (coe w [ b ])) ⟩
          Trunc-fmap (merid X) (transport Codes (merid X x₀) [ b ]) ∎;

        p = ap2
          (λ p₁ → λ p₂ →
            transport P (merid X x₀) [ up x₀ ]
              =⟨ transport-Trunc (λ y → north X == y) (merid X x₀) (up x₀) ⟩
            [ transport (λ y → north X == y) (merid X x₀) (up x₀) ]
              =⟨ ap [_] $ trans-pathfrom {A = Suspension X} (merid X x₀) (up x₀) ⟩
            [ (merid X x₀ ∙ ! (merid X x₀)) ∙ merid X x₀ ]
              =⟨ ap [_] p₁ ⟩
            [ merid X x₀ ]
              =⟨ idp ⟩
            Trunc-fmap (merid X) [ x₀ ]
              =⟨ ap (Trunc-fmap (merid X)) (! p₂) ⟩
            Trunc-fmap (merid X) (Codes-mer x₀ [ x₀ ])
              =⟨ ap (Trunc-fmap (merid X)) (! (coe-β (Codes-mer-equiv x₀) [ x₀ ])) ⟩
            Trunc-fmap (merid X) (coe (ua (Codes-mer-equiv x₀)) [ x₀ ])
              =⟨ ! (SuspensionRec.glue-β X _ _ (ua ∘ Codes-mer-equiv) x₀)
                |in-ctx (λ w → Trunc-fmap (merid X) (coe w [ x₀ ])) ⟩
            Trunc-fmap (merid X) (transport Codes (merid X x₀) [ x₀ ]) ∎)
          (coh (merid X x₀)) Codes-mer-coh}
          where
            coh : {s₁ s₂ : Suspension X} (p : s₁ == s₂)
              → (ap (λ s → s ∙ p) (!-inv-r p))
                == ∙-assoc p (! p) p ∙ ap (λ s → p ∙ s) (!-inv-l p) ∙ ∙-unit-r p
            coh idp = idp

      STS : (x' : X) (c : Codes (north X)) → 
        transport P (merid X x') (Trunc-fmap up c)
        == Trunc-fmap (merid X) (transport Codes (merid X x') c)
      STS x' = Trunc-elim (λ _ → =-preserves-level _ Trunc-level) 
                          (WedgeExt.ext STS-args x')


  decode-encode : {x : Suspension X} (tα : P x) 
    → decode {x} (encode {x} tα) == tα
  decode-encode {x} tα = Trunc-elim 
    {B = λ tα → decode {x} (encode {x} tα) == tα}
    (λ _ → =-preserves-level k Trunc-level)
    (J (λ y p → decode {y} (encode {y} [ p ]) == [ p ]) 
       (ap [_] (!-inv-r (merid X x₀))))
    tα

  eqv : Trunc k X ≃ Trunc k (north X == north X)
  eqv = equiv decodeN encode decode-encode encode-decodeN

  path : Trunc k X == Trunc k (north X == north X)
  path = ua eqv
