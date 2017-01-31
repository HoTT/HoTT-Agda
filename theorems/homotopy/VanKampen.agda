{-# OPTIONS --without-K --rewriting #-}

open import HoTT
import homotopy.RelativelyConstantToSetExtendsViaSurjection as SurjExt

module homotopy.VanKampen {i j k l}
  (span : Span {i} {j} {k})
  {D : Type l} (h : D → Span.C span) (h-is-surj : is-surj h) where

  open Span span
  open import homotopy.vankampen.CodeAP span h h-is-surj
  open import homotopy.vankampen.CodeBP span h h-is-surj
  open import homotopy.vankampen.Code span h h-is-surj

  -- favonia: [pPP] means path from [P] to [P].
  encode-idp : ∀ p → code p p
  encode-idp = Pushout-elim {P = λ p → code p p}
    (λ a → q[ ⟧a idp₀ ]) (λ b → q[ ⟧b idp₀ ]) lemma where
    abstract
      lemma : ∀ c → q[ ⟧a idp₀ ] == q[ ⟧b idp₀ ] [ (λ p → code p p) ↓ glue c ]
      lemma = SurjExt.ext
        (λ c → ↓-preserves-set SetQuot-is-set)
        h h-is-surj
        (λ d → from-transp (λ p → code p p) (glue (h d)) $
          transport (λ p → code p p) (glue (h d)) q[ ⟧a idp₀ ]
            =⟨ ap (λ pPP → coe pPP q[ pc-a idp₀ ]) ((! (ap2-diag code (glue (h d)))) ∙ ap2-out code (glue (h d)) (glue (h d))) ⟩
          coe (ap (λ p₀ → code p₀ (left (f (h d)))) (glue (h d)) ∙ ap (codeBP (g (h d))) (glue (h d))) q[ ⟧a idp₀ ]
            =⟨ coe-∙ (ap (λ p₀ → code p₀ (left (f (h d)))) (glue (h d))) (ap (codeBP (g (h d))) (glue (h d))) q[ pc-a idp₀ ] ⟩
          transport (codeBP (g (h d))) (glue (h d)) (transport (λ p₀ → code p₀ (left (f (h d)))) (glue (h d)) q[ ⟧a idp₀ ])
            =⟨ transp-cPA-glue d (⟧a idp₀) |in-ctx transport (λ p₁ → code (right (g (h d))) p₁) (glue (h d)) ⟩
          transport (codeBP (g (h d))) (glue (h d)) q[ ⟧b idp₀ bb⟦ d ⟧a idp₀ ]
            =⟨ transp-cBP-glue d (⟧b idp₀ bb⟦ d ⟧a idp₀) ⟩
          q[ ⟧b idp₀ bb⟦ d ⟧a idp₀ ba⟦ d ⟧b idp₀ ]
            =⟨ quot-rel (pcBBr-idp₀-idp₀ (pc-b idp₀)) ⟩
          q[ ⟧b idp₀ ]
            =∎)
        (λ _ _ _ → prop-has-all-paths-↓ $ ↓-level SetQuot-is-set)

  encode : ∀ {p₀ p₁} → p₀ =₀ p₁ → code p₀ p₁
  encode {p₀} {p₁} pPP = transport₀ (code p₀) (code-is-set {p₀} {p₁}) pPP (encode-idp p₀)

  abstract
    decode-encode-idp : ∀ p → decode {p} {p} (encode-idp p) == idp₀
    decode-encode-idp = Pushout-elim
      {P = λ p → decode {p} {p} (encode-idp p) == idp₀}
      (λ _ → idp) (λ _ → idp)
      (λ c → prop-has-all-paths-↓ (Trunc-level {n = 0} idp₀ (idp₀ :> Trunc 0 (right (g c) == _))))

    decode-encode' : ∀ {p₀ p₁} (pPP : p₀ == p₁) → decode {p₀} {p₁} (encode [ pPP ]) == [ pPP ]
    decode-encode' idp = decode-encode-idp _

    decode-encode : ∀ {p₀ p₁} (pPP : p₀ =₀ p₁) → decode {p₀} {p₁} (encode pPP) == pPP
    decode-encode = Trunc-elim (λ _ → =-preserves-set Trunc-level) decode-encode'

  abstract
    transp-idcAA-r : ∀ {a₀ a₁} (p : a₀ == a₁) -- [idc] = identity code
      → transport (codeAA a₀) p q[ ⟧a idp₀ ] == q[ ⟧a [ p ] ]
    transp-idcAA-r idp = idp

    encode-decodeAA : ∀ {a₀ a₁} (c : precodeAA a₀ a₁)
      → encode (decodeAA q[ c ]) == q[ c ]
    encode-decodeAB : ∀ {a₀ b₁} (c : precodeAB a₀ b₁)
      → encode (decodeAB q[ c ]) == q[ c ]
    encode-decodeAA {a₀} (pc-a pA) = Trunc-elim
      {P = λ pA → encode (decodeAA q[ ⟧a pA ]) == q[ ⟧a pA ]}
      (λ _ → =-preserves-set SetQuot-is-set)
      (λ pA →
        transport (codeAP a₀) (ap left pA) q[ ⟧a idp₀ ]
          =⟨ ap (λ e → coe e q[ ⟧a idp₀ ]) (∘-ap (codeAP a₀) left pA) ⟩
        transport (codeAA a₀) pA q[ ⟧a idp₀ ]
          =⟨ transp-idcAA-r pA ⟩
        q[ ⟧a [ pA ] ]
          =∎)
      pA
    encode-decodeAA {a₀} (pc-aba d pc pA) = Trunc-elim
      {P = λ pA → encode (decodeAA q[ pc ab⟦ d ⟧a pA ]) == q[ pc ab⟦ d ⟧a pA ]}
      (λ _ → =-preserves-set SetQuot-is-set)
      (λ pA →
        encode (decodeAB q[ pc ] ∙₀' [ ! (glue (h d)) ∙' ap left pA ])
          =⟨ transp₀-∙₀' (λ p₁ → code-is-set {left a₀} {p₁}) (decodeAB q[ pc ]) [ ! (glue (h d)) ∙' ap left pA ] (encode-idp (left a₀)) ⟩
        transport (codeAP a₀) (! (glue (h d)) ∙' ap left pA) (encode (decodeAB q[ pc ]))
          =⟨ ap (transport (codeAP a₀) (! (glue (h d)) ∙' ap left pA)) (encode-decodeAB pc) ⟩
        transport (codeAP a₀) (! (glue (h d)) ∙' ap left pA) q[ pc ]
          =⟨ transp-∙' {B = codeAP a₀} (! (glue (h d))) (ap left pA) q[ pc ] ⟩
        transport (codeAP a₀) (ap left pA) (transport (codeAP a₀) (! (glue (h d))) q[ pc ])
          =⟨ ap (transport (codeAP a₀) (ap left pA)) (transp-cAP-!glue d pc) ⟩
        transport (codeAP a₀) (ap left pA) q[ pc ab⟦ d ⟧a idp₀ ]
          =⟨ ap (λ e → coe e q[ pc ab⟦ d ⟧a idp₀ ]) (∘-ap (codeAP a₀) left pA) ⟩
        transport (codeAA a₀) pA q[ pc ab⟦ d ⟧a idp₀ ]
          =⟨ transp-cAA-r d pA (pc ab⟦ d ⟧a idp₀) ⟩
        q[ pc ab⟦ d ⟧a idp₀ aa⟦ d ⟧b idp₀ ab⟦ d ⟧a [ pA ] ]
          =⟨ quot-rel (pcAAr-cong (pcABr-idp₀-idp₀ pc) [ pA ]) ⟩
        q[ pc ab⟦ d ⟧a [ pA ] ]
          =∎)
      pA
    encode-decodeAB {a₀} (pc-aab d pc pB) = Trunc-elim
      {P = λ pB → encode (decodeAB q[ pc aa⟦ d ⟧b pB ]) == q[ pc aa⟦ d ⟧b pB ]}
      (λ _ → =-preserves-set SetQuot-is-set)
      (λ pB →
        encode (decodeAA q[ pc ] ∙₀' [ glue (h d) ∙' ap right pB ])
          =⟨ transp₀-∙₀' (λ p₁ → code-is-set {left a₀} {p₁}) (decodeAA q[ pc ]) [ glue (h d) ∙' ap right pB ] (encode-idp (left a₀)) ⟩
        transport (codeAP a₀) (glue (h d) ∙' ap right pB) (encode (decodeAA q[ pc ]))
          =⟨ ap (transport (codeAP a₀) (glue (h d) ∙' ap right pB)) (encode-decodeAA pc) ⟩
        transport (codeAP a₀) (glue (h d) ∙' ap right pB) q[ pc ]
          =⟨ transp-∙' {B = codeAP a₀} (glue (h d)) (ap right pB) q[ pc ] ⟩
        transport (codeAP a₀) (ap right pB) (transport (codeAP a₀) (glue (h d)) q[ pc ])
          =⟨ ap (transport (codeAP a₀) (ap right pB)) (transp-cAP-glue d pc) ⟩
        transport (codeAP a₀) (ap right pB) q[ pc aa⟦ d ⟧b idp₀ ]
          =⟨ ap (λ e → coe e q[ pc aa⟦ d ⟧b idp₀ ]) (∘-ap (codeAP a₀) right pB) ⟩
        transport (codeAB a₀) pB q[ pc aa⟦ d ⟧b idp₀ ]
          =⟨ transp-cAB-r d pB (pc aa⟦ d ⟧b idp₀) ⟩
        q[ pc aa⟦ d ⟧b idp₀ ab⟦ d ⟧a idp₀ aa⟦ d ⟧b [ pB ] ]
          =⟨ quot-rel (pcABr-cong (pcAAr-idp₀-idp₀ pc) [ pB ]) ⟩
        q[ pc aa⟦ d ⟧b [ pB ] ]
          =∎)
      pB


  abstract
    transp-idcBB-r : ∀ {b₀ b₁} (p : b₀ == b₁) -- [idc] = identity code
      → transport (codeBB b₀) p q[ ⟧b idp₀ ] == q[ ⟧b [ p ] ]
    transp-idcBB-r idp = idp

    encode-decodeBA : ∀ {b₀ a₁} (c : precodeBA b₀ a₁)
      → encode (decodeBA q[ c ]) == q[ c ]
    encode-decodeBB : ∀ {b₀ b₁} (c : precodeBB b₀ b₁)
      → encode (decodeBB q[ c ]) == q[ c ]
    encode-decodeBA {b₀} (pc-bba d pc pA) = Trunc-elim
      {P = λ pA → encode (decodeBA q[ pc bb⟦ d ⟧a pA ]) == q[ pc bb⟦ d ⟧a pA ]}
      (λ _ → =-preserves-set SetQuot-is-set)
      (λ pA →
        encode (decodeBB q[ pc ] ∙₀' [ ! (glue (h d)) ∙' ap left pA ])
          =⟨ transp₀-∙₀' (λ p₁ → code-is-set {right b₀} {p₁}) (decodeBB q[ pc ]) [ ! (glue (h d)) ∙' ap left pA ] (encode-idp (right b₀)) ⟩
        transport (codeBP b₀) (! (glue (h d)) ∙' ap left pA) (encode (decodeBB q[ pc ]))
          =⟨ ap (transport (codeBP b₀) (! (glue (h d)) ∙' ap left pA)) (encode-decodeBB pc) ⟩
        transport (codeBP b₀) (! (glue (h d)) ∙' ap left pA) q[ pc ]
          =⟨ transp-∙' {B = codeBP b₀} (! (glue (h d))) (ap left pA) q[ pc ] ⟩
        transport (codeBP b₀) (ap left pA) (transport (codeBP b₀) (! (glue (h d))) q[ pc ])
          =⟨ ap (transport (codeBP b₀) (ap left pA)) (transp-cBP-!glue d pc) ⟩
        transport (codeBP b₀) (ap left pA) q[ pc bb⟦ d ⟧a idp₀ ]
          =⟨ ap (λ e → coe e q[ pc bb⟦ d ⟧a idp₀ ]) (∘-ap (codeBP b₀) left pA) ⟩
        transport (codeBA b₀) pA q[ pc bb⟦ d ⟧a idp₀ ]
          =⟨ transp-cBA-r d pA (pc bb⟦ d ⟧a idp₀) ⟩
        q[ pc bb⟦ d ⟧a idp₀ ba⟦ d ⟧b idp₀ bb⟦ d ⟧a [ pA ] ]
          =⟨ quot-rel (pcBAr-cong (pcBBr-idp₀-idp₀ pc) [ pA ]) ⟩
        q[ pc bb⟦ d ⟧a [ pA ] ]
          =∎)
      pA
    encode-decodeBB {b₀} (pc-b pB) = Trunc-elim
      {P = λ pB → encode (decodeBB q[ ⟧b pB ]) == q[ ⟧b pB ]}
      (λ _ → =-preserves-set SetQuot-is-set)
      (λ pB →
        transport (codeBP b₀) (ap right pB) q[ ⟧b idp₀ ]
          =⟨ ap (λ e → coe e q[ ⟧b idp₀ ]) (∘-ap (codeBP b₀) right pB) ⟩
        transport (codeBB b₀) pB q[ ⟧b idp₀ ]
          =⟨ transp-idcBB-r pB ⟩
        q[ ⟧b [ pB ] ]
          =∎)
      pB
    encode-decodeBB {b₀} (pc-bab d pc pB) = Trunc-elim
      {P = λ pB → encode (decodeBB q[ pc ba⟦ d ⟧b pB ]) == q[ pc ba⟦ d ⟧b pB ]}
      (λ _ → =-preserves-set SetQuot-is-set)
      (λ pB →
        encode (decodeBA q[ pc ] ∙₀' [ glue (h d) ∙' ap right pB ])
          =⟨ transp₀-∙₀' (λ p₁ → code-is-set {right b₀} {p₁}) (decodeBA q[ pc ]) [ glue (h d) ∙' ap right pB ] (encode-idp (right b₀)) ⟩
        transport (codeBP b₀) (glue (h d) ∙' ap right pB) (encode (decodeBA q[ pc ]))
          =⟨ ap (transport (codeBP b₀) (glue (h d) ∙' ap right pB)) (encode-decodeBA pc) ⟩
        transport (codeBP b₀) (glue (h d) ∙' ap right pB) q[ pc ]
          =⟨ transp-∙' {B = codeBP b₀} (glue (h d)) (ap right pB) q[ pc ] ⟩
        transport (codeBP b₀) (ap right pB) (transport (codeBP b₀) (glue (h d)) q[ pc ])
          =⟨ ap (transport (codeBP b₀) (ap right pB)) (transp-cBP-glue d pc) ⟩
        transport (codeBP b₀) (ap right pB) q[ pc ba⟦ d ⟧b idp₀ ]
          =⟨ ap (λ e → coe e q[ pc ba⟦ d ⟧b idp₀ ]) (∘-ap (codeBP b₀) right pB) ⟩
        transport (codeBB b₀) pB q[ pc ba⟦ d ⟧b idp₀ ]
          =⟨ transp-cBB-r d pB (pc ba⟦ d ⟧b idp₀) ⟩
        q[ pc ba⟦ d ⟧b idp₀ bb⟦ d ⟧a idp₀ ba⟦ d ⟧b [ pB ] ]
          =⟨ quot-rel (pcBBr-cong (pcBAr-idp₀-idp₀ pc) [ pB ]) ⟩
        q[ pc ba⟦ d ⟧b [ pB ] ]
          =∎)
      pB

  abstract
    encode-decode : ∀ {p₀ p₁} (cPP : code p₀ p₁)
      → encode {p₀} {p₁} (decode {p₀} {p₁} cPP) == cPP
    encode-decode {p₀} {p₁} = Pushout-elim
      {P = λ p₀ → ∀ p₁ → (cPP : code p₀ p₁) → encode (decode {p₀} {p₁} cPP) == cPP}
      (λ a₀ → Pushout-elim
        (λ a₁ → SetQuot-elim
          {P = λ cPP → encode (decodeAA cPP) == cPP}
          (λ _ → =-preserves-set SetQuot-is-set)
          (encode-decodeAA {a₀} {a₁})
          (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _)))
        (λ b₁ → SetQuot-elim
          {P = λ cPP → encode (decodeAB cPP) == cPP}
          (λ _ → =-preserves-set SetQuot-is-set)
          (encode-decodeAB {a₀} {b₁})
          (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _)))
        (λ _ → prop-has-all-paths-↓ $ Π-is-prop λ cPP → SetQuot-is-set _ _))
      (λ b₀ → Pushout-elim
        (λ a₁ → SetQuot-elim
          {P = λ cPP → encode (decodeBA cPP) == cPP}
          (λ _ → =-preserves-set SetQuot-is-set)
          (encode-decodeBA {b₀} {a₁})
          (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _)))
        (λ b₁ → SetQuot-elim
          {P = λ cPP → encode (decodeBB cPP) == cPP}
          (λ _ → =-preserves-set SetQuot-is-set)
          (encode-decodeBB {b₀} {b₁})
          (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _)))
        (λ _ → prop-has-all-paths-↓ $ Π-is-prop λ cPP → SetQuot-is-set _ _))
      (λ _ → prop-has-all-paths-↓ $ Π-is-prop λ p₁ → Π-is-prop λ cPP → codeBP-is-set {p₁ = p₁} _ _)
      p₀ p₁

  vankampen : ∀ p₀ p₁ → (p₀ =₀ p₁) ≃ code p₀ p₁
  vankampen p₀ p₁ = equiv (encode {p₀} {p₁}) (decode {p₀} {p₁}) (encode-decode {p₀} {p₁}) (decode-encode {p₀} {p₁})
