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
  cAA-to-cBA d₀ = SetQuot-rec SetQuot-level (q[_] ∘ pcAA-to-pcBA d₀) (quot-rel ∘ pcAA-to-pcBA-rel d₀)
  cAB-to-cBB : ∀ d₀ {b} → codeAB (f (h d₀)) b → codeBB (g (h d₀)) b
  cAB-to-cBB d₀ = SetQuot-rec SetQuot-level (q[_] ∘ pcAB-to-pcBB d₀) (quot-rel ∘ pcAB-to-pcBB-rel d₀)

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
  cBA-to-cAA d₀ = SetQuot-rec SetQuot-level (q[_] ∘ pcBA-to-pcAA d₀) (quot-rel ∘ pcBA-to-pcAA-rel d₀)
  cBB-to-cAB : ∀ d₀ {b} → codeBB (g (h d₀)) b → codeAB (f (h d₀)) b
  cBB-to-cAB d₀ = SetQuot-rec SetQuot-level (q[_] ∘ pcBB-to-pcAB d₀) (quot-rel ∘ pcBB-to-pcAB-rel d₀)

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

    eqv-in-image : (d₀ : D) → codeAA (f (h d₀)) a₁ ≃ codeBA (g (h d₀)) a₁
    eqv-in-image d₀ = equiv to from to-from from-to where
      to : codeAA (f (h d₀)) a₁ → codeBA (g (h d₀)) a₁
      to = cAA-to-cBA d₀

      from : codeBA (g (h d₀)) a₁ → codeAA (f (h d₀)) a₁
      from = cBA-to-cAA d₀

      abstract
        to-from : ∀ cBA → to (from cBA) == cBA
        to-from = SetQuot-elim
          (λ _ → =-preserves-set SetQuot-is-set)
          (pcBA-to-pcAA-to-pcBA d₀)
          (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _))

        from-to : ∀ cAA → from (to cAA) == cAA
        from-to = SetQuot-elim
          (λ _ → =-preserves-set SetQuot-is-set)
          (pcAA-to-pcBA-to-pcAA d₀)
          (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _))

    abstract
      eqv-is-const : ∀ d₁ d₂ (p : h d₁ == h d₂)
        → eqv-in-image d₁ == eqv-in-image d₂
        [ (λ c → codeAA (f c) a₁ ≃ codeBA (g c) a₁) ↓ p ]
      eqv-is-const d₁ d₂ p = ↓-Subtype-in (λ d → is-equiv-prop) $
        ↓-→-from-transp $ λ= $
          SetQuot-elim (λ _ → =-preserves-set SetQuot-is-set)
            (λ pcAA →
              transport (λ c → codeBA (g c) a₁) p q[ pcAA-to-pcBA d₁ pcAA ]
                =⟨ ap-∘ (λ b → codeBA b a₁) g p |in-ctx (λ p → coe p q[ pcAA-to-pcBA d₁ pcAA ]) ⟩
              transport (λ b → codeBA b a₁) (ap g p) q[ pcAA-to-pcBA d₁ pcAA ]
                =⟨ transp-cBA-l d₁ (pcAA-to-pcBA d₁ pcAA) (ap g p) ⟩
              q[ pcBA-prepend d₁ [ ! $ ap g p ] (pcAA-to-pcBA d₁ pcAA) ]
                =⟨ !-ap g p |in-ctx (λ p → q[ pcBA-prepend d₁ [ p ] (pcAA-to-pcBA d₁ pcAA) ]) ⟩
              q[ pcBA-prepend d₁ [ ap g (! p) ] (pcAA-to-pcBA d₁ pcAA) ]
                =⟨ pcAA-lemma d₁ d₂ (! p) pcAA ⟩
              q[ pcAA-to-pcBA d₂ (pcAA-prepend d₁ [ ap f (! p) ] pcAA) ]
                =⟨ ap-! f p |in-ctx (λ p → q[ pcAA-to-pcBA d₂ (pcAA-prepend d₁ [ p ] pcAA) ]) ⟩
              q[ pcAA-to-pcBA d₂ (pcAA-prepend d₁ [ ! $ ap f p ] pcAA) ]
                =⟨ ! $ transp-cAA-l d₁ pcAA (ap f p) |in-ctx cAA-to-cBA d₂ ⟩
              cAA-to-cBA d₂ (transport (λ a → codeAA a a₁) (ap f p) q[ pcAA ])
                =⟨ ∘-ap (λ c → codeAA c a₁) f p |in-ctx (λ p → coe p q[ pcAA ]) |in-ctx cAA-to-cBA d₂ ⟩
              cAA-to-cBA d₂ (transport (λ c → codeAA (f c) a₁) p q[ pcAA ])
                =∎)
            (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _))

    module SE = SurjExt
      (λ c → ≃-is-set SetQuot-is-set SetQuot-is-set)
      h h-is-surj
      eqv-in-image
      eqv-is-const

    abstract
      eqv : ∀ c → codeAA (f c) a₁ ≃ codeBA (g c) a₁
      eqv = SE.surj-ext

      eqv-β : ∀ d → eqv (h d) == eqv-in-image d
      eqv-β = SE.surj-ext-β

  module CodeABEquivCodeBB (b₁ : B) where

    eqv-in-image : (d₀ : D) → codeAB (f (h d₀)) b₁ ≃ codeBB (g (h d₀)) b₁
    eqv-in-image d₀ = equiv to from to-from from-to where
      to : codeAB (f (h d₀)) b₁ → codeBB (g (h d₀)) b₁
      to = cAB-to-cBB d₀

      from : codeBB (g (h d₀)) b₁ → codeAB (f (h d₀)) b₁
      from = cBB-to-cAB d₀

      abstract
        to-from : ∀ cBB → to (from cBB) == cBB
        to-from = SetQuot-elim
          (λ _ → =-preserves-set SetQuot-is-set)
          (pcBB-to-pcAB-to-pcBB d₀)
          (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _))

        from-to : ∀ cAB → from (to cAB) == cAB
        from-to = SetQuot-elim
          (λ _ → =-preserves-set SetQuot-is-set)
          (pcAB-to-pcBB-to-pcAB d₀)
          (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _))

    abstract
      eqv-is-const : ∀ d₁ d₂ (p : h d₁ == h d₂)
        → eqv-in-image d₁ == eqv-in-image d₂
        [ (λ c → codeAB (f c) b₁ ≃ codeBB (g c) b₁) ↓ p ]
      eqv-is-const d₁ d₂ p = ↓-Subtype-in (λ d → is-equiv-prop) $
        ↓-→-from-transp $ λ= $
          SetQuot-elim (λ _ → =-preserves-set SetQuot-is-set)
            (λ pcAB →
              transport (λ c → codeBB (g c) b₁) p q[ pcAB-to-pcBB d₁ pcAB ]
                =⟨ ap-∘ (λ b → codeBB b b₁) g p |in-ctx (λ p → coe p q[ pcAB-to-pcBB d₁ pcAB ]) ⟩
              transport (λ b → codeBB b b₁) (ap g p) q[ pcAB-to-pcBB d₁ pcAB ]
                =⟨ transp-cBB-l d₁ (pcAB-to-pcBB d₁ pcAB) (ap g p) ⟩
              q[ pcBB-prepend d₁ [ ! $ ap g p ] (pcAB-to-pcBB d₁ pcAB) ]
                =⟨ !-ap g p |in-ctx (λ p → q[ pcBB-prepend d₁ [ p ] (pcAB-to-pcBB d₁ pcAB) ]) ⟩
              q[ pcBB-prepend d₁ [ ap g (! p) ] (pcAB-to-pcBB d₁ pcAB) ]
                =⟨ pcAB-lemma d₁ d₂ (! p) pcAB ⟩
              q[ pcAB-to-pcBB d₂ (pcAB-prepend d₁ [ ap f (! p) ] pcAB) ]
                =⟨ ap-! f p |in-ctx (λ p → q[ pcAB-to-pcBB d₂ (pcAB-prepend d₁ [ p ] pcAB) ]) ⟩
              q[ pcAB-to-pcBB d₂ (pcAB-prepend d₁ [ ! $ ap f p ] pcAB) ]
                =⟨ ! $ transp-cAB-l d₁ pcAB (ap f p) |in-ctx cAB-to-cBB d₂ ⟩
              cAB-to-cBB d₂ (transport (λ a → codeAB a b₁) (ap f p) q[ pcAB ])
                =⟨ ∘-ap (λ c → codeAB c b₁) f p |in-ctx (λ p → coe p q[ pcAB ]) |in-ctx cAB-to-cBB d₂ ⟩
              cAB-to-cBB d₂ (transport (λ c → codeAB (f c) b₁) p q[ pcAB ])
                =∎)
            (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _))

    module SE = SurjExt
      (λ c → ≃-is-set SetQuot-is-set SetQuot-is-set)
      h h-is-surj
      eqv-in-image
      eqv-is-const

    abstract
      eqv : ∀ c → codeAB (f c) b₁ ≃ codeBB (g c) b₁
      eqv = SE.surj-ext

      eqv-β : ∀ d → eqv (h d) == eqv-in-image d
      eqv-β = SE.surj-ext-β

  module EqvPAIdEqvPB where
    abstract
      path-in-image : ∀ d₀ d₁
        →  CodeAAEquivCodeBA.eqv (f (h d₁)) (h d₀)
        == CodeABEquivCodeBB.eqv (g (h d₁)) (h d₀)
        [ (λ p → codeAP (f (h d₀)) p ≃ codeBP (g (h d₀)) p) ↓ glue (h d₁) ]
      path-in-image d₀ d₁ =
        CodeAAEquivCodeBA.eqv-β (f (h d₁)) d₀
        ∙ᵈ lemma
        ∙'ᵈ ! (CodeABEquivCodeBB.eqv-β (g (h d₁)) d₀) where
        lemma : CodeAAEquivCodeBA.eqv-in-image (f (h d₁)) d₀
             == CodeABEquivCodeBB.eqv-in-image (g (h d₁)) d₀
             [ (λ p → codeAP (f (h d₀)) p ≃ codeBP (g (h d₀)) p) ↓ glue (h d₁) ]
        lemma = ↓-Subtype-in (λ d → is-equiv-prop) $
          ↓-→-from-transp $ λ= $ SetQuot-elim
            (λ _ → =-preserves-set SetQuot-is-set)
            (λ pcAA →
              transport (λ p → codeBP (g (h d₀)) p) (glue (h d₁)) q[ pcAA-to-pcBA d₀ pcAA ]
                =⟨ CodeBP.glue-β (g (h d₀)) (h d₁) |in-ctx (λ p → coe p q[ pcAA-to-pcBA d₀ pcAA ]) ⟩
              coe (ua (CodeBAEquivCodeBB.eqv (g (h d₀)) (h d₁))) q[ pcAA-to-pcBA d₀ pcAA ]
                =⟨ CodeBAEquivCodeBB.eqv-β (g (h d₀)) d₁ |in-ctx (λ e → coe (ua e) q[ pcAA-to-pcBA d₀ pcAA ]) ⟩
              coe (ua (CodeBAEquivCodeBB.eqv-in-image (g (h d₀)) d₁)) q[ pcAA-to-pcBA d₀ pcAA ]
                =⟨ coe-β (CodeBAEquivCodeBB.eqv-in-image (g (h d₀)) d₁) q[ pcAA-to-pcBA d₀ pcAA ] ⟩
              q[ pcAA-to-pcBA d₀ pcAA ba⟦ d₁ ⟧b idp₀ ]
                =⟨ idp ⟩
              q[ pcAB-to-pcBB d₀ (pcAA aa⟦ d₁ ⟧b idp₀) ]
                =⟨ ! $ coe-β (CodeAAEquivCodeAB.eqv-in-image (f (h d₀)) d₁) q[ pcAA ] |in-ctx cAB-to-cBB d₀ ⟩
              cAB-to-cBB d₀ (coe (ua (CodeAAEquivCodeAB.eqv-in-image (f (h d₀)) d₁)) q[ pcAA ])
                =⟨ ! $ CodeAAEquivCodeAB.eqv-β (f (h d₀)) d₁ |in-ctx (λ e → cAB-to-cBB d₀ (coe (ua e) q[ pcAA ])) ⟩
              cAB-to-cBB d₀ (coe (ua (CodeAAEquivCodeAB.eqv (f (h d₀)) (h d₁))) q[ pcAA ])
                =⟨ ! $ CodeAP.glue-β (f (h d₀)) (h d₁) |in-ctx (λ p → cAB-to-cBB d₀ (coe p q[ pcAA ])) ⟩
              cAB-to-cBB d₀ (transport (λ p → codeAP (f (h d₀)) p) (glue (h d₁)) q[ pcAA ])
                =∎)
            (λ _ → prop-has-all-paths-↓ $ SetQuot-is-set _ _)

    abstract
      path : ∀ c₀ c₁
        →  CodeAAEquivCodeBA.eqv (f c₁) c₀
        == CodeABEquivCodeBB.eqv (g c₁) c₀
        [ (λ p → codeAP (f c₀) p ≃ codeBP (g c₀) p) ↓ glue c₁ ]
      path = SurjExt.surj-ext
        (λ c₀ → Π-is-set λ c₁ → ↓-preserves-level $ ≃-is-set SetQuot-is-set SetQuot-is-set)
        h h-is-surj
        (λ d₀ → SurjExt.surj-ext
          (λ c₁ → ↓-preserves-level $ ≃-is-set SetQuot-is-set SetQuot-is-set)
          h h-is-surj
          (λ d₁ → path-in-image d₀ d₁)
          (λ _ _ _ → prop-has-all-paths-↓ $ ↓-level $ ≃-is-set SetQuot-is-set SetQuot-is-set))
        (λ _ _ _ → prop-has-all-paths-↓ $ Π-is-prop λ _ → ↓-level $ ≃-is-set SetQuot-is-set SetQuot-is-set)


  cAP-equiv-cBP : ∀ c₀ p₁ → codeAP (f c₀) p₁ ≃ codeBP (g c₀) p₁
  cAP-equiv-cBP c₀ = Pushout-elim
    {P = λ p₁ → codeAP (f c₀) p₁ ≃ codeBP (g c₀) p₁}
    (λ a₁ → CodeAAEquivCodeBA.eqv a₁ c₀)
    (λ b₁ → CodeABEquivCodeBB.eqv b₁ c₀)
    (λ c₁ → EqvPAIdEqvPB.path c₀ c₁)

  module Code = PushoutRec
    {D = Pushout span → Type (lmax (lmax (lmax i j) k) l)}
    codeAP codeBP (λ c₀ → λ= λ p₁ → ua (cAP-equiv-cBP c₀ p₁))

  code : Pushout span → Pushout span → Type (lmax (lmax (lmax i j) k) l)
  code = Code.f

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
    cAA-to-path-is-cBA-to-path : ∀ {a₁} c₀ →
      cAA-to-path {f c₀} {a₁} == cBA-to-path {g c₀} {a₁}
      [ (λ p₀ → code p₀ (left a₁) → p₀ =₀ left a₁) ↓ glue c₀ ]
    cAA-to-path-is-cBA-to-path {a₁ = a₁} = SurjExt.surj-ext
      (λ _ → ↓-preserves-level $ Π-is-set λ _ → Trunc-level) h h-is-surj
      (λ d₀ → ↓-→-from-transp $ λ= $ SetQuot-elim
        {P = λ cAA → transport (_=₀ left a₁) (glue (h d₀)) (cAA-to-path cAA)
                  == cBA-to-path (transport (λ p₀ → code p₀ (left a₁)) (glue (h d₀)) cAA)}
        (λ _ → =-preserves-set Trunc-level)
        (λ pcAA →
          transport (_=₀ left a₁) (glue (h d₀)) (pcAA-to-path pcAA)
            =⟨ transp₀-idf=₀cst [ glue (h d₀) ] (pcAA-to-path pcAA) ⟩
          !₀ [ glue (h d₀) ] ∙₀ pcAA-to-path pcAA
            =⟨ ∙₀=∙₀' [ ! (glue (h d₀)) ] (pcAA-to-path pcAA) ⟩
          !₀ [ glue (h d₀) ] ∙₀' pcAA-to-path pcAA
            =⟨ ! $ pcAA-to-pcBA-to-path d₀ pcAA ⟩
          pcBA-to-path (pcAA-to-pcBA d₀ pcAA)
            =⟨ ! $ ap (λ e → cBA-to-path (–> e q[ pcAA ])) (CodeAAEquivCodeBA.eqv-β a₁ d₀) ⟩
          cBA-to-path (–> (CodeAAEquivCodeBA.eqv a₁ (h d₀)) q[ pcAA ])
            =⟨ ! $ ap cBA-to-path (coe-β (CodeAAEquivCodeBA.eqv a₁ (h d₀)) q[ pcAA ]) ⟩
          cBA-to-path (coe (ua (CodeAAEquivCodeBA.eqv a₁ (h d₀))) q[ pcAA ])
            =⟨ ! $ ap (λ p → cBA-to-path (coe p q[ pcAA ])) (app=-β (ua ∘ cAP-equiv-cBP (h d₀)) (left a₁)) ⟩
          cBA-to-path (coe (app= (λ= λ p₁ → ua (cAP-equiv-cBP (h d₀) p₁)) (left a₁)) q[ pcAA ])
            =⟨ ! $ ap (λ p → cBA-to-path (coe (app= p (left a₁)) q[ pcAA ])) (Code.glue-β (h d₀)) ⟩
          cBA-to-path (coe (app= (ap code (glue (h d₀))) (left a₁)) q[ pcAA ])
            =⟨ ap (λ p → cBA-to-path (coe p q[ pcAA ])) (∘-ap (λ f₁ → f₁ (left a₁)) code (glue (h d₀))) ⟩
          cBA-to-path (transport (λ p₀ → code p₀ (left a₁)) (glue (h d₀)) q[ pcAA ])
            =∎)
        (λ _ → prop-has-all-paths-↓ $ Trunc-level {n = 0} _ _))
      (λ _ _ _ → prop-has-all-paths-↓ $ ↓-level $ Π-is-set λ _ → Trunc-level)

  abstract
    cAB-to-path-is-cBB-to-path : ∀ {b₁} c₀ →
      cAB-to-path {f c₀} {b₁} == cBB-to-path {g c₀} {b₁}
      [ (λ p₀ → code p₀ (right b₁) → p₀ =₀ right b₁) ↓ glue c₀ ]
    cAB-to-path-is-cBB-to-path {b₁ = b₁} = SurjExt.surj-ext
      (λ _ → ↓-preserves-level $ Π-is-set λ _ → Trunc-level) h h-is-surj
      (λ d₀ → ↓-→-from-transp $ λ= $ SetQuot-elim
        {P = λ cAB → transport (_=₀ right b₁) (glue (h d₀)) (cAB-to-path cAB)
                  == cBB-to-path (transport (λ p₀ → code p₀ (right b₁)) (glue (h d₀)) cAB)}
        (λ _ → =-preserves-set Trunc-level)
        (λ pcAB →
          transport (_=₀ right b₁) (glue (h d₀)) (pcAB-to-path pcAB)
            =⟨ transp₀-idf=₀cst [ glue (h d₀) ] (pcAB-to-path pcAB) ⟩
          !₀ [ glue (h d₀) ] ∙₀ pcAB-to-path pcAB
            =⟨ ∙₀=∙₀' [ ! (glue (h d₀)) ] (pcAB-to-path pcAB) ⟩
          !₀ [ glue (h d₀) ] ∙₀' pcAB-to-path pcAB
            =⟨ ! $ pcAB-to-pcBB-to-path d₀ pcAB ⟩
          pcBB-to-path (pcAB-to-pcBB d₀ pcAB)
            =⟨ ! $ ap (λ e → cBB-to-path (–> e q[ pcAB ])) (CodeABEquivCodeBB.eqv-β b₁ d₀) ⟩
          cBB-to-path (–> (CodeABEquivCodeBB.eqv b₁ (h d₀)) q[ pcAB ])
            =⟨ ! $ ap cBB-to-path (coe-β (CodeABEquivCodeBB.eqv b₁ (h d₀)) q[ pcAB ]) ⟩
          cBB-to-path (coe (ua (CodeABEquivCodeBB.eqv b₁ (h d₀))) q[ pcAB ])
            =⟨ ! $ ap (λ p → cBB-to-path (coe p q[ pcAB ])) (app=-β (ua ∘ cAP-equiv-cBP (h d₀)) (right b₁)) ⟩
          cBB-to-path (coe (app= (λ= λ p₁ → ua (cAP-equiv-cBP (h d₀) p₁)) (right b₁)) q[ pcAB ])
            =⟨ ! $ ap (λ p → cBB-to-path (coe (app= p (right b₁)) q[ pcAB ])) (Code.glue-β (h d₀)) ⟩
          cBB-to-path (coe (app= (ap code (glue (h d₀))) (right b₁)) q[ pcAB ])
            =⟨ ap (λ p → cBB-to-path (coe p q[ pcAB ])) (∘-ap (λ f₁ → f₁ (right b₁)) code (glue (h d₀))) ⟩
          cBB-to-path (transport (λ p₀ → code p₀ (right b₁)) (glue (h d₀)) q[ pcAB ])
            =∎)
        (λ _ → prop-has-all-paths-↓ $ Trunc-level {n = 0} _ _))
      (λ _ _ _ → prop-has-all-paths-↓ $ ↓-level $ Π-is-set λ _ → Trunc-level)

  code-to-path : ∀ {p₀ p₁} → code p₀ p₁ → p₀ =₀ p₁
  code-to-path {p₀} {p₁} = Pushout-elim
    {P = λ p₀ → code p₀ p₁ → p₀ =₀ p₁}
    (λ a₀ → cAP-to-path {a₀} {p₁})
    (λ b₀ → cBP-to-path {b₀} {p₁})
    (λ c₀ → Pushout-elim
      {P = λ p₁ → cAP-to-path {f c₀} {p₁} == cBP-to-path {g c₀} {p₁}
        [ (λ p₀ → code p₀ p₁ → p₀ =₀ p₁) ↓ glue c₀ ]}
      (λ a₁ → cAA-to-path-is-cBA-to-path {a₁ = a₁} c₀)
      (λ b₁ → cAB-to-path-is-cBB-to-path {b₁ = b₁} c₀)
      (λ _ → prop-has-all-paths-↓ $ ↓-level $ Π-is-set λ _ → Trunc-level)
      p₁)
    p₀
