{-# OPTIONS --without-K --rewriting #-}

open import HoTT
import homotopy.RelativelyConstantToSetExtendsViaSurjection as SurjExt

module homotopy.vankampen.Code {i j k l}
  (span : Span {i} {j} {k})
  {D : Type l} (h : D → Span.C span) (h-is-surj : is-surj h) where

  open Span span
  open import homotopy.vankampen.CodeAP span h h-is-surj
  open import homotopy.vankampen.CodeBP span h h-is-surj

  pcAA-to-pcBA : ∀ d₀ {a} → precodeAA (f (h d₀)) a → precodeBA (g (h d₀)) a
  pcAB-to-pcBB : ∀ d₀ {b} → precodeAB (f (h d₀)) b → precodeBB (g (h d₀)) b
  pcAA-to-pcBA d₀ (pc-a pA) = pc-bba d₀ (pc-b idp₀) pA
  pcAA-to-pcBA d₀ (pc-aba d pc pA) = pc-bba d (pcAB-to-pcBB d₀ pc) pA
  pcAB-to-pcBB d₀ (pc-aab d pc pB) = pc-bab d (pcAA-to-pcBA d₀ pc) pB

  abstract
    pcAA-to-pcBA-rel : ∀ d₀ {a} {pcAA₁ pcAA₂ : precodeAA (f (h d₀)) a}
      → precodeAA-rel pcAA₁ pcAA₂
      → precodeBA-rel (pcAA-to-pcBA d₀ pcAA₁) (pcAA-to-pcBA d₀ pcAA₂)
    pcAB-to-pcBB-rel : ∀ d₀ {a} {pcAB₁ pcAB₂ : precodeAB (f (h d₀)) a}
      → precodeAB-rel pcAB₁ pcAB₂
      → precodeBB-rel (pcAB-to-pcBB d₀ pcAB₁) (pcAB-to-pcBB d₀ pcAB₂)
    pcAA-to-pcBA-rel d₀ (pcAAr-idp₀-idp₀ pcAA) = pcBAr-idp₀-idp₀ (pcAA-to-pcBA d₀ pcAA)
    pcAA-to-pcBA-rel d₀ (pcAAr-cong r pA) = pcBAr-cong (pcAB-to-pcBB-rel d₀ r) pA
    pcAB-to-pcBB-rel d₀ (pcABr-idp₀-idp₀ pcAB) = pcBBr-idp₀-idp₀ (pcAB-to-pcBB d₀ pcAB)
    pcAB-to-pcBB-rel d₀ (pcABr-switch pcAB pC) = pcBBr-switch (pcAB-to-pcBB d₀ pcAB) pC
    pcAB-to-pcBB-rel d₀ (pcABr-cong r pB) = pcBBr-cong (pcAA-to-pcBA-rel d₀ r) pB

  cAA-to-cBA : ∀ d₀ {a} → codeAA (f (h d₀)) a → codeBA (g (h d₀)) a
  cAA-to-cBA d₀ = SetQuot-rec (q[_] ∘ pcAA-to-pcBA d₀) (quot-rel ∘ pcAA-to-pcBA-rel d₀)
  cAB-to-cBB : ∀ d₀ {b} → codeAB (f (h d₀)) b → codeBB (g (h d₀)) b
  cAB-to-cBB d₀ = SetQuot-rec (q[_] ∘ pcAB-to-pcBB d₀) (quot-rel ∘ pcAB-to-pcBB-rel d₀)

  -- BX to AX
  pcBA-to-pcAA : ∀ d₀ {a} → precodeBA (g (h d₀)) a → precodeAA (f (h d₀)) a
  pcBB-to-pcAB : ∀ d₀ {b} → precodeBB (g (h d₀)) b → precodeAB (f (h d₀)) b
  pcBA-to-pcAA d₀ (pc-bba d pc pA) = pc-aba d (pcBB-to-pcAB d₀ pc) pA
  pcBB-to-pcAB d₀ (pc-b pB) = pc-aab d₀ (pc-a idp₀) pB
  pcBB-to-pcAB d₀ (pc-bab d pc pB) = pc-aab d (pcBA-to-pcAA d₀ pc) pB

  abstract
    pcBA-to-pcAA-rel : ∀ d₀ {a} {pcBA₁ pcBA₂ : precodeBA (g (h d₀)) a}
      → precodeBA-rel pcBA₁ pcBA₂
      → precodeAA-rel (pcBA-to-pcAA d₀ pcBA₁) (pcBA-to-pcAA d₀ pcBA₂)
    pcBB-to-pcAB-rel : ∀ d₀ {a} {pcBB₁ pcBB₂ : precodeBB (g (h d₀)) a}
      → precodeBB-rel pcBB₁ pcBB₂
      → precodeAB-rel (pcBB-to-pcAB d₀ pcBB₁) (pcBB-to-pcAB d₀ pcBB₂)
    pcBA-to-pcAA-rel d₀ (pcBAr-idp₀-idp₀ pcBA) = pcAAr-idp₀-idp₀ (pcBA-to-pcAA d₀ pcBA)
    pcBA-to-pcAA-rel d₀ (pcBAr-cong r pA) = pcAAr-cong (pcBB-to-pcAB-rel d₀ r) pA
    pcBB-to-pcAB-rel d₀ (pcBBr-idp₀-idp₀ pcBB) = pcABr-idp₀-idp₀ (pcBB-to-pcAB d₀ pcBB)
    pcBB-to-pcAB-rel d₀ (pcBBr-switch pcBB pC) = pcABr-switch (pcBB-to-pcAB d₀ pcBB) pC
    pcBB-to-pcAB-rel d₀ (pcBBr-cong r pB) = pcABr-cong (pcBA-to-pcAA-rel d₀ r) pB

  cBA-to-cAA : ∀ d₀ {a} → codeBA (g (h d₀)) a → codeAA (f (h d₀)) a
  cBA-to-cAA d₀ = SetQuot-rec (q[_] ∘ pcBA-to-pcAA d₀) (quot-rel ∘ pcBA-to-pcAA-rel d₀)
  cBB-to-cAB : ∀ d₀ {b} → codeBB (g (h d₀)) b → codeAB (f (h d₀)) b
  cBB-to-cAB d₀ = SetQuot-rec (q[_] ∘ pcBB-to-pcAB d₀) (quot-rel ∘ pcBB-to-pcAB-rel d₀)

  -- roundtrips
  abstract
    pcBA-to-pcAA-to-pcBA : ∀ d₀ {a} (pcBA : precodeBA _ a)
      → q[ pcAA-to-pcBA d₀ (pcBA-to-pcAA d₀ pcBA) ] == q[ pcBA ] :> codeBA _ a
    pcBB-to-pcAB-to-pcBB : ∀ d₀ {b} (pcBB : precodeBB _ b)
      → q[ pcAB-to-pcBB d₀ (pcBB-to-pcAB d₀ pcBB) ] == q[ pcBB ] :> codeBB _ b
    pcBA-to-pcAA-to-pcBA d₀ (pc-bba d pc pA) = pcBB-to-pcAB-to-pcBB d₀ pc |in-ctx λ c → c-bba d c pA
    pcBB-to-pcAB-to-pcBB d₀ (pc-b pB) = pcBB-idp₀-idp₀-head pB
    pcBB-to-pcAB-to-pcBB d₀ (pc-bab d pc pB) = pcBA-to-pcAA-to-pcBA d₀ pc |in-ctx λ c → c-bab d c pB

    pcAA-to-pcBA-to-pcAA : ∀ d₀ {a} (pcAA : precodeAA _ a)
      → q[ pcBA-to-pcAA d₀ (pcAA-to-pcBA d₀ pcAA) ] == q[ pcAA ] :> codeAA _ a
    pcAB-to-pcBB-to-pcAB : ∀ d₀ {b} (pcAB : precodeAB _ b)
      → q[ pcBB-to-pcAB d₀ (pcAB-to-pcBB d₀ pcAB) ] == q[ pcAB ] :> codeAB _ b
    pcAA-to-pcBA-to-pcAA d₀ (pc-aba d pc pA) = pcAB-to-pcBB-to-pcAB d₀ pc |in-ctx λ c → c-aba d c pA
    pcAA-to-pcBA-to-pcAA d₀ (pc-a pA) = pcAA-idp₀-idp₀-head pA
    pcAB-to-pcBB-to-pcAB d₀ (pc-aab d pc pB) = pcAA-to-pcBA-to-pcAA d₀ pc |in-ctx λ c → c-aab d c pB

  private
    pcAA-lemma : ∀ d₁ d₂ {a₁} (p : h d₂ == h d₁) (pcAA : precodeAA _ a₁)
      →  q[ pcBA-prepend d₁ [ ap g p ] (pcAA-to-pcBA d₁ pcAA) ]
      == q[ pcAA-to-pcBA d₂ (pcAA-prepend d₁ [ ap f p ] pcAA) ]
    pcAB-lemma : ∀ d₁ d₂ {b₁} (p : h d₂ == h d₁) (pcAB : precodeAB _ b₁)
      →  q[ pcBB-prepend d₁ [ ap g p ] (pcAB-to-pcBB d₁ pcAB) ]
      == q[ pcAB-to-pcBB d₂ (pcAB-prepend d₁ [ ap f p ] pcAB) ]
    pcAA-lemma d₁ d₂ p (pc-a pA) = ap (λ c → c-bba d₁ c pA) $ ! $
      q[ ⟧b idp₀ bb⟦ _ ⟧a [ ap f p ] ba⟦ _ ⟧b idp₀ ]
        =⟨ quot-rel (pcBBr-switch (⟧b idp₀) [ p ]) ⟩
      q[ ⟧b idp₀ bb⟦ _ ⟧a idp₀ ba⟦ _ ⟧b [ ap g p ] ]
        =⟨ pcBB-idp₀-idp₀-head [ ap g p ] ⟩
      q[ ⟧b [ ap g p ] ]
        =⟨ ! (quot-rel (pcBBr-idp₀-idp₀ (pc-b [ ap g p ]))) ⟩
      q[ ⟧b [ ap g p ] bb⟦ _ ⟧a idp₀ ba⟦ _ ⟧b idp₀ ]
        =∎
    pcAA-lemma d₁ d₂ p (pc-aba d pc pA) = pcAB-lemma d₁ d₂ p pc |in-ctx (λ c → c-bba d c pA)
    pcAB-lemma d₁ d₂ p (pc-aab d pc pB) = pcAA-lemma d₁ d₂ p pc |in-ctx (λ c → c-bab d c pB)

  module CodeAAEquivCodeBA (a₁ : A) where

    eqv-on-image : (d₀ : D) → codeAA (f (h d₀)) a₁ ≃ codeBA (g (h d₀)) a₁
    eqv-on-image d₀ = equiv to from to-from from-to where
      to : codeAA (f (h d₀)) a₁ → codeBA (g (h d₀)) a₁
      to = cAA-to-cBA d₀

      from : codeBA (g (h d₀)) a₁ → codeAA (f (h d₀)) a₁
      from = cBA-to-cAA d₀

      abstract
        to-from : ∀ cBA → to (from cBA) == cBA
        to-from = SetQuot-elim
          (pcBA-to-pcAA-to-pcBA d₀)
          (λ _ → prop-has-all-paths-↓)

        from-to : ∀ cAA → from (to cAA) == cAA
        from-to = SetQuot-elim
          (pcAA-to-pcBA-to-pcAA d₀)
          (λ _ → prop-has-all-paths-↓)

    abstract
      eqv-is-const : ∀ d₁ d₂ (p : h d₁ == h d₂)
        → eqv-on-image d₁ == eqv-on-image d₂
        [ (λ c → codeAA (f c) a₁ ≃ codeBA (g c) a₁) ↓ p ]
      eqv-is-const d₁ d₂ p = ↓-Subtype-in (λ d → is-equiv-prop) $
        ↓-→-from-transp $ λ= $
          SetQuot-elim
            (λ pcAA →
              transport (λ c → codeBA (g c) a₁) p q[ pcAA-to-pcBA d₁ pcAA ]
                =⟨ ap-∘ (λ b → codeBA b a₁) g p |in-ctx (λ p → coe p q[ pcAA-to-pcBA d₁ pcAA ]) ⟩
              transport (λ b → codeBA b a₁) (ap g p) q[ pcAA-to-pcBA d₁ pcAA ]
                =⟨ transp-cBA-l d₁ (ap g p) (pcAA-to-pcBA d₁ pcAA) ⟩
              q[ pcBA-prepend d₁ [ ! $ ap g p ] (pcAA-to-pcBA d₁ pcAA) ]
                =⟨ !-ap g p |in-ctx (λ p → q[ pcBA-prepend d₁ [ p ] (pcAA-to-pcBA d₁ pcAA) ]) ⟩
              q[ pcBA-prepend d₁ [ ap g (! p) ] (pcAA-to-pcBA d₁ pcAA) ]
                =⟨ pcAA-lemma d₁ d₂ (! p) pcAA ⟩
              q[ pcAA-to-pcBA d₂ (pcAA-prepend d₁ [ ap f (! p) ] pcAA) ]
                =⟨ ap-! f p |in-ctx (λ p → q[ pcAA-to-pcBA d₂ (pcAA-prepend d₁ [ p ] pcAA) ]) ⟩
              q[ pcAA-to-pcBA d₂ (pcAA-prepend d₁ [ ! $ ap f p ] pcAA) ]
                =⟨ ! $ transp-cAA-l d₁ (ap f p) pcAA |in-ctx cAA-to-cBA d₂ ⟩
              cAA-to-cBA d₂ (transport (λ a → codeAA a a₁) (ap f p) q[ pcAA ])
                =⟨ ∘-ap (λ c → codeAA c a₁) f p |in-ctx (λ p → coe p q[ pcAA ]) |in-ctx cAA-to-cBA d₂ ⟩
              cAA-to-cBA d₂ (transport (λ c → codeAA (f c) a₁) p q[ pcAA ])
                =∎)
            (λ _ → prop-has-all-paths-↓)

    module SE = SurjExt
      h h-is-surj
      eqv-on-image
      eqv-is-const

    abstract
      eqv : ∀ c → codeAA (f c) a₁ ≃ codeBA (g c) a₁
      eqv = SE.ext

      eqv-β : ∀ d → eqv (h d) == eqv-on-image d
      eqv-β = SE.β

  module CodeABEquivCodeBB (b₁ : B) where

    eqv-on-image : (d₀ : D) → codeAB (f (h d₀)) b₁ ≃ codeBB (g (h d₀)) b₁
    eqv-on-image d₀ = equiv to from to-from from-to where
      to : codeAB (f (h d₀)) b₁ → codeBB (g (h d₀)) b₁
      to = cAB-to-cBB d₀

      from : codeBB (g (h d₀)) b₁ → codeAB (f (h d₀)) b₁
      from = cBB-to-cAB d₀

      abstract
        to-from : ∀ cBB → to (from cBB) == cBB
        to-from = SetQuot-elim
          (pcBB-to-pcAB-to-pcBB d₀)
          (λ _ → prop-has-all-paths-↓)

        from-to : ∀ cAB → from (to cAB) == cAB
        from-to = SetQuot-elim
          (pcAB-to-pcBB-to-pcAB d₀)
          (λ _ → prop-has-all-paths-↓)

    abstract
      eqv-is-const : ∀ d₁ d₂ (p : h d₁ == h d₂)
        → eqv-on-image d₁ == eqv-on-image d₂
        [ (λ c → codeAB (f c) b₁ ≃ codeBB (g c) b₁) ↓ p ]
      eqv-is-const d₁ d₂ p = ↓-Subtype-in (λ d → is-equiv-prop) $
        ↓-→-from-transp $ λ= $
          SetQuot-elim
            (λ pcAB →
              transport (λ c → codeBB (g c) b₁) p q[ pcAB-to-pcBB d₁ pcAB ]
                =⟨ ap-∘ (λ b → codeBB b b₁) g p |in-ctx (λ p → coe p q[ pcAB-to-pcBB d₁ pcAB ]) ⟩
              transport (λ b → codeBB b b₁) (ap g p) q[ pcAB-to-pcBB d₁ pcAB ]
                =⟨ transp-cBB-l d₁ (ap g p) (pcAB-to-pcBB d₁ pcAB) ⟩
              q[ pcBB-prepend d₁ [ ! $ ap g p ] (pcAB-to-pcBB d₁ pcAB) ]
                =⟨ !-ap g p |in-ctx (λ p → q[ pcBB-prepend d₁ [ p ] (pcAB-to-pcBB d₁ pcAB) ]) ⟩
              q[ pcBB-prepend d₁ [ ap g (! p) ] (pcAB-to-pcBB d₁ pcAB) ]
                =⟨ pcAB-lemma d₁ d₂ (! p) pcAB ⟩
              q[ pcAB-to-pcBB d₂ (pcAB-prepend d₁ [ ap f (! p) ] pcAB) ]
                =⟨ ap-! f p |in-ctx (λ p → q[ pcAB-to-pcBB d₂ (pcAB-prepend d₁ [ p ] pcAB) ]) ⟩
              q[ pcAB-to-pcBB d₂ (pcAB-prepend d₁ [ ! $ ap f p ] pcAB) ]
                =⟨ ! $ transp-cAB-l d₁ (ap f p) pcAB |in-ctx cAB-to-cBB d₂ ⟩
              cAB-to-cBB d₂ (transport (λ a → codeAB a b₁) (ap f p) q[ pcAB ])
                =⟨ ∘-ap (λ c → codeAB c b₁) f p |in-ctx (λ p → coe p q[ pcAB ]) |in-ctx cAB-to-cBB d₂ ⟩
              cAB-to-cBB d₂ (transport (λ c → codeAB (f c) b₁) p q[ pcAB ])
                =∎)
            (λ _ → prop-has-all-paths-↓)

    module SE = SurjExt
      h h-is-surj
      eqv-on-image
      eqv-is-const

    abstract
      eqv : ∀ c → codeAB (f c) b₁ ≃ codeBB (g c) b₁
      eqv = SE.ext

      eqv-β : ∀ d → eqv (h d) == eqv-on-image d
      eqv-β = SE.β

  module EqvPAIdEqvPB where
    abstract
      path-on-image : ∀ d₀ d₁
        →  CodeAAEquivCodeBA.eqv (f (h d₁)) (h d₀)
        == CodeABEquivCodeBB.eqv (g (h d₁)) (h d₀)
        [ (λ p → codeAP (f (h d₀)) p ≃ codeBP (g (h d₀)) p) ↓ glue (h d₁) ]
      path-on-image d₀ d₁ =
        CodeAAEquivCodeBA.eqv-β (f (h d₁)) d₀
        ∙ᵈ lemma
        ∙'ᵈ ! (CodeABEquivCodeBB.eqv-β (g (h d₁)) d₀) where
        lemma : CodeAAEquivCodeBA.eqv-on-image (f (h d₁)) d₀
             == CodeABEquivCodeBB.eqv-on-image (g (h d₁)) d₀
             [ (λ p → codeAP (f (h d₀)) p ≃ codeBP (g (h d₀)) p) ↓ glue (h d₁) ]
        lemma = ↓-Subtype-in (λ d → is-equiv-prop) $
          ↓-→-from-transp $ λ= $ SetQuot-elim
            (λ pcAA →
              transport (λ p → codeBP (g (h d₀)) p) (glue (h d₁)) q[ pcAA-to-pcBA d₀ pcAA ]
                =⟨ transp-cBP-glue d₁ (pcAA-to-pcBA d₀ pcAA) ⟩
              q[ pcAA-to-pcBA d₀ pcAA ba⟦ d₁ ⟧b idp₀ ]
                =⟨ ! $ transp-cAP-glue d₁ pcAA |in-ctx cAB-to-cBB d₀ ⟩
              cAB-to-cBB d₀ (transport (λ p → codeAP (f (h d₀)) p) (glue (h d₁)) q[ pcAA ])
                =∎)
            (λ _ → prop-has-all-paths-↓)

    abstract
      path : ∀ c₀ c₁
        →  CodeAAEquivCodeBA.eqv (f c₁) c₀
        == CodeABEquivCodeBB.eqv (g c₁) c₀
        [ (λ p → codeAP (f c₀) p ≃ codeBP (g c₀) p) ↓ glue c₁ ]
      path = SurjExt.ext
        {{Π-level (λ _ → ↓-preserves-level ⟨⟩)}}
        h h-is-surj
        (λ d₀ → SurjExt.ext
          {{↓-preserves-level ⟨⟩}}
          h h-is-surj
          (λ d₁ → path-on-image d₀ d₁)
          (λ _ _ _ → prop-has-all-paths-↓ {{↓-level ⟨⟩}}))
        (λ _ _ _ → prop-has-all-paths-↓ {{Π-level (λ _ → ↓-level ⟨⟩)}})


  cAP-equiv-cBP : ∀ c₀ p₁ → codeAP (f c₀) p₁ ≃ codeBP (g c₀) p₁
  cAP-equiv-cBP c₀ = Pushout-elim
    {P = λ p₁ → codeAP (f c₀) p₁ ≃ codeBP (g c₀) p₁}
    (λ a₁ → CodeAAEquivCodeBA.eqv a₁ c₀)
    (λ b₁ → CodeABEquivCodeBB.eqv b₁ c₀)
    (λ c₁ → EqvPAIdEqvPB.path c₀ c₁)

  module Code = PushoutRec
    {D = Pushout span → Type (lmax (lmax (lmax i j) k) l)}
    codeAP codeBP (λ c₀ → λ= $ ua ∘ cAP-equiv-cBP c₀)

  code : Pushout span → Pushout span → Type (lmax (lmax (lmax i j) k) l)
  code = Code.f

  abstract
    code-level : ∀ {p₀ p₁} → is-set (code p₀ p₁)
    code-level {p₀} {p₁} = Pushout-elim
      {P = λ p₀ → ∀ p₁ → is-set (code p₀ p₁)}
      (λ a₀ p₁ → codeAP-level {a₀} {p₁})
      (λ b₀ p₁ → codeBP-level {b₀} {p₁})
      (λ c₀ → prop-has-all-paths-↓)
      p₀ p₁

  code-is-set = code-level

  abstract
    transp-cPA-glue : ∀ d₀ {a₁} (pcAA : precodeAA (f (h d₀)) a₁)
      → transport (λ p₀ → code p₀ (left a₁)) (glue (h d₀)) q[ pcAA  ] == q[ pcAA-to-pcBA d₀ pcAA ]
    transp-cPA-glue d₀ {a₁} pcAA =
      transport (λ p₀ → code p₀ (left a₁)) (glue (h d₀)) q[ pcAA  ]
        =⟨ ap (λ e → coe e q[ pcAA ])
            ( ap-∘ (_$ left a₁) code (glue (h d₀))
            ∙ ap (ap (_$ left a₁)) (Code.glue-β (h d₀))
            ∙ app=-β (ua ∘ cAP-equiv-cBP (h d₀)) (left a₁)
            ∙ ap ua (CodeAAEquivCodeBA.eqv-β a₁ d₀)) ⟩
      coe (ua (CodeAAEquivCodeBA.eqv-on-image a₁ d₀)) q[ pcAA  ]
        =⟨ coe-β (CodeAAEquivCodeBA.eqv-on-image a₁ d₀) q[ pcAA ] ⟩
      q[ pcAA-to-pcBA d₀ pcAA ]
        =∎

    transp-cPB-glue : ∀ d₀ {b₁} (pcAB : precodeAB (f (h d₀)) b₁)
      → transport (λ p₀ → code p₀ (right b₁)) (glue (h d₀)) q[ pcAB  ] == q[ pcAB-to-pcBB d₀ pcAB ]
    transp-cPB-glue d₀ {b₁} pcAB =
      transport (λ p₀ → code p₀ (right b₁)) (glue (h d₀)) q[ pcAB  ]
        =⟨ ap (λ e → coe e q[ pcAB ])
            ( ap-∘ (_$ right b₁) code (glue (h d₀))
            ∙ ap (ap (_$ right b₁)) (Code.glue-β (h d₀))
            ∙ app=-β (ua ∘ cAP-equiv-cBP (h d₀)) (right b₁)
            ∙ ap ua (CodeABEquivCodeBB.eqv-β b₁ d₀)) ⟩
      coe (ua (CodeABEquivCodeBB.eqv-on-image b₁ d₀)) q[ pcAB  ]
        =⟨ coe-β (CodeABEquivCodeBB.eqv-on-image b₁ d₀) q[ pcAB ] ⟩
      q[ pcAB-to-pcBB d₀ pcAB ]
        =∎

  -- code to path
  abstract
    pcAA-to-pcBA-to-path : ∀ d₀ {a₁} (pcAA : precodeAA _ a₁) →
         pcBA-to-path (pcAA-to-pcBA d₀ pcAA)
      == !₀ [ glue (h d₀) ] ∙₀' pcAA-to-path pcAA
    pcAB-to-pcBB-to-path : ∀ d₀ {b₁} (pcAB : precodeAB _ b₁) →
         pcBB-to-path (pcAB-to-pcBB d₀ pcAB)
      == !₀ [ glue (h d₀) ] ∙₀' pcAB-to-path pcAB
    pcAA-to-pcBA-to-path d₀ (pc-a pA) = ∙₀'-unit-l (!₀ [ glue (h d₀) ] ∙₀' ap₀ left pA)
    pcAA-to-pcBA-to-path d₀ (pc-aba d pc pA) =
        ap (λ p → p ∙₀' !₀ [ glue (h d) ] ∙₀' ap₀ left pA) (pcAB-to-pcBB-to-path d₀ pc)
      ∙ ∙₀'-assoc (!₀ [ glue (h d₀) ]) (pcAB-to-path pc) (!₀ [ glue (h d) ] ∙₀' ap₀ left pA)
    pcAB-to-pcBB-to-path d₀ (pc-aab d pc pB) =
        ap (λ p → p ∙₀' [ glue (h d) ] ∙₀' ap₀ right pB) (pcAA-to-pcBA-to-path d₀ pc)
      ∙ ∙₀'-assoc (!₀ [ glue (h d₀) ]) (pcAA-to-path pc) ([ glue (h d) ] ∙₀' ap₀ right pB)

  abstract
    decodeAA-is-decodeBA : ∀ {a₁} c₀ →
      decodeAA {f c₀} {a₁} == decodeBA {g c₀} {a₁}
      [ (λ p₀ → code p₀ (left a₁) → p₀ =₀ left a₁) ↓ glue c₀ ]
    decodeAA-is-decodeBA {a₁ = a₁} = SurjExt.ext
      {{↓-preserves-level ⟨⟩}} h h-is-surj
      (λ d₀ → ↓-→-from-transp $ λ= $ SetQuot-elim
        {P = λ cAA → transport (_=₀ left a₁) (glue (h d₀)) (decodeAA cAA)
                  == decodeBA (transport (λ p₀ → code p₀ (left a₁)) (glue (h d₀)) cAA)}
        (λ pcAA →
          transport (_=₀ left a₁) (glue (h d₀)) (pcAA-to-path pcAA)
            =⟨ transp₀-idf=₀cst [ glue (h d₀) ] (pcAA-to-path pcAA) ⟩
          !₀ [ glue (h d₀) ] ∙₀ pcAA-to-path pcAA
            =⟨ ∙₀=∙₀' [ ! (glue (h d₀)) ] (pcAA-to-path pcAA) ⟩
          !₀ [ glue (h d₀) ] ∙₀' pcAA-to-path pcAA
            =⟨ ! $ pcAA-to-pcBA-to-path d₀ pcAA ⟩
          pcBA-to-path (pcAA-to-pcBA d₀ pcAA)
            =⟨ ! $ ap (λ e → decodeBA (–> e q[ pcAA ])) (CodeAAEquivCodeBA.eqv-β a₁ d₀) ⟩
          decodeBA (–> (CodeAAEquivCodeBA.eqv a₁ (h d₀)) q[ pcAA ])
            =⟨ ! $ ap decodeBA (coe-β (CodeAAEquivCodeBA.eqv a₁ (h d₀)) q[ pcAA ]) ⟩
          decodeBA (coe (ua (CodeAAEquivCodeBA.eqv a₁ (h d₀))) q[ pcAA ])
            =⟨ ! $ ap (λ p → decodeBA (coe p q[ pcAA ])) (app=-β (ua ∘ cAP-equiv-cBP (h d₀)) (left a₁)) ⟩
          decodeBA (coe (app= (λ= λ p₁ → ua (cAP-equiv-cBP (h d₀) p₁)) (left a₁)) q[ pcAA ])
            =⟨ ! $ ap (λ p → decodeBA (coe (app= p (left a₁)) q[ pcAA ])) (Code.glue-β (h d₀)) ⟩
          decodeBA (coe (app= (ap code (glue (h d₀))) (left a₁)) q[ pcAA ])
            =⟨ ap (λ p → decodeBA (coe p q[ pcAA ])) (∘-ap (λ f₁ → f₁ (left a₁)) code (glue (h d₀))) ⟩
          decodeBA (transport (λ p₀ → code p₀ (left a₁)) (glue (h d₀)) q[ pcAA ])
            =∎)
        (λ _ → prop-has-all-paths-↓))
      (λ _ _ _ → prop-has-all-paths-↓ {{↓-level ⟨⟩}})

  abstract
    decodeAB-is-decodeBB : ∀ {b₁} c₀ →
      decodeAB {f c₀} {b₁} == decodeBB {g c₀} {b₁}
      [ (λ p₀ → code p₀ (right b₁) → p₀ =₀ right b₁) ↓ glue c₀ ]
    decodeAB-is-decodeBB {b₁ = b₁} = SurjExt.ext
      {{↓-preserves-level ⟨⟩}} h h-is-surj
      (λ d₀ → ↓-→-from-transp $ λ= $ SetQuot-elim
        {P = λ cAB → transport (_=₀ right b₁) (glue (h d₀)) (decodeAB cAB)
                  == decodeBB (transport (λ p₀ → code p₀ (right b₁)) (glue (h d₀)) cAB)}
        (λ pcAB →
          transport (_=₀ right b₁) (glue (h d₀)) (pcAB-to-path pcAB)
            =⟨ transp₀-idf=₀cst [ glue (h d₀) ] (pcAB-to-path pcAB) ⟩
          !₀ [ glue (h d₀) ] ∙₀ pcAB-to-path pcAB
            =⟨ ∙₀=∙₀' [ ! (glue (h d₀)) ] (pcAB-to-path pcAB) ⟩
          !₀ [ glue (h d₀) ] ∙₀' pcAB-to-path pcAB
            =⟨ ! $ pcAB-to-pcBB-to-path d₀ pcAB ⟩
          pcBB-to-path (pcAB-to-pcBB d₀ pcAB)
            =⟨ ! $ ap (λ e → decodeBB (–> e q[ pcAB ])) (CodeABEquivCodeBB.eqv-β b₁ d₀) ⟩
          decodeBB (–> (CodeABEquivCodeBB.eqv b₁ (h d₀)) q[ pcAB ])
            =⟨ ! $ ap decodeBB (coe-β (CodeABEquivCodeBB.eqv b₁ (h d₀)) q[ pcAB ]) ⟩
          decodeBB (coe (ua (CodeABEquivCodeBB.eqv b₁ (h d₀))) q[ pcAB ])
            =⟨ ! $ ap (λ p → decodeBB (coe p q[ pcAB ])) (app=-β (ua ∘ cAP-equiv-cBP (h d₀)) (right b₁)) ⟩
          decodeBB (coe (app= (λ= λ p₁ → ua (cAP-equiv-cBP (h d₀) p₁)) (right b₁)) q[ pcAB ])
            =⟨ ! $ ap (λ p → decodeBB (coe (app= p (right b₁)) q[ pcAB ])) (Code.glue-β (h d₀)) ⟩
          decodeBB (coe (app= (ap code (glue (h d₀))) (right b₁)) q[ pcAB ])
            =⟨ ap (λ p → decodeBB (coe p q[ pcAB ])) (∘-ap (λ f₁ → f₁ (right b₁)) code (glue (h d₀))) ⟩
          decodeBB (transport (λ p₀ → code p₀ (right b₁)) (glue (h d₀)) q[ pcAB ])
            =∎)
        (λ _ → prop-has-all-paths-↓))
      (λ _ _ _ → prop-has-all-paths-↓ {{↓-level ⟨⟩}})

  abstract
    decodeAP-is-decodeBP : ∀ c₀ p₁
      → decodeAP {f c₀} {p₁} == decodeBP {g c₀} {p₁}
        [ (λ p₀ → code p₀ p₁ → p₀ =₀ p₁) ↓ glue c₀ ]
    decodeAP-is-decodeBP c₀ = Pushout-elim
      {P = λ p₁ → decodeAP {f c₀} {p₁} == decodeBP {g c₀} {p₁}
        [ (λ p₀ → code p₀ p₁ → p₀ =₀ p₁) ↓ glue c₀ ]}
      (λ a₁ → decodeAA-is-decodeBA {a₁ = a₁} c₀)
      (λ b₁ → decodeAB-is-decodeBB {b₁ = b₁} c₀)
      (λ _ → prop-has-all-paths-↓ {{↓-level ⟨⟩}})

  decode : ∀ {p₀ p₁} → code p₀ p₁ → p₀ =₀ p₁
  decode {p₀} {p₁} = Pushout-elim
    {P = λ p₀ → code p₀ p₁ → p₀ =₀ p₁}
    (λ a₀ → decodeAP {a₀} {p₁})
    (λ b₀ → decodeBP {b₀} {p₁})
    (λ c₀ → decodeAP-is-decodeBP c₀ p₁)
    p₀
