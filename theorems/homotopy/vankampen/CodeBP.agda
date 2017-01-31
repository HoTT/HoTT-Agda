{-# OPTIONS --without-K --rewriting #-}

{- Remember to keep CodeAP.agda in sync. -}

open import HoTT
import homotopy.RelativelyConstantToSetExtendsViaSurjection as SurjExt

module homotopy.vankampen.CodeBP {i j k l}
  (span : Span {i} {j} {k})
  {D : Type l} (h : D → Span.C span) (h-is-surj : is-surj h) where

  open Span span

  data precodeBB (b₀ : B) : B → Type (lmax (lmax (lmax i j) k) l)
  data precodeBA (b₀ : B) (a₁ : A) : Type (lmax (lmax (lmax i j) k) l)

  data precodeBB b₀ where
    pc-b : ∀ {b₁} (pB : b₀ =₀ b₁) → precodeBB b₀ b₁
    pc-bab : ∀ d {b₁} (pc : precodeBA b₀ (f (h d))) (pB : g (h d) =₀ b₁) → precodeBB b₀ b₁

  infix 66 pc-b
  syntax pc-b p = ⟧b p
  infixl 65 pc-bab
  syntax pc-bab d pcBA pB = pcBA ba⟦ d ⟧b pB

  data precodeBA b₀ a₁ where
    pc-bba : ∀ d (pc : precodeBB b₀ (g (h d))) (pA : f (h d) =₀ a₁) → precodeBA b₀ a₁

  infixl 65 pc-bba
  syntax pc-bba d pcBB pA = pcBB bb⟦ d ⟧a pA

  data precodeBB-rel {b₀ : B} : {b₁ : B}
    → precodeBB b₀ b₁ → precodeBB b₀ b₁ → Type (lmax (lmax (lmax i j) k) l)
  data precodeBA-rel {b₀ : B} : {a₁ : A}
    → precodeBA b₀ a₁ → precodeBA b₀ a₁ → Type (lmax (lmax (lmax i j) k) l)
  data precodeBB-rel {b₀} where
    pcBBr-idp₀-idp₀ : ∀ {d} pcBB → precodeBB-rel (pcBB bb⟦ d ⟧a idp₀ ba⟦ d ⟧b idp₀) pcBB
    pcBBr-switch : ∀ {d₀ d₁ : D} pcBB (pC : h d₀ =₀ h d₁)
      → precodeBB-rel (pcBB bb⟦ d₀ ⟧a ap₀ f pC ba⟦ d₁ ⟧b idp₀) (pcBB bb⟦ d₀ ⟧a idp₀ ba⟦ d₀ ⟧b ap₀ g pC)
    pcBBr-cong : ∀ {d b₁ pcBA₁ pcBA₂} (r : precodeBA-rel pcBA₁ pcBA₂) (pB : g (h d) =₀ b₁)
      → precodeBB-rel (pcBA₁ ba⟦ d ⟧b pB) (pcBA₂ ba⟦ d ⟧b pB)
  data precodeBA-rel {b₀} where
    pcBAr-idp₀-idp₀ : ∀ {d} pcBA → precodeBA-rel (pcBA ba⟦ d ⟧b idp₀ bb⟦ d ⟧a idp₀) pcBA
    pcBAr-cong : ∀ {d a₁ pcBB₁ pcBB₂} (r : precodeBB-rel pcBB₁ pcBB₂) (pA : f (h d) =₀ a₁)
      → precodeBA-rel (pcBB₁ bb⟦ d ⟧a pA) (pcBB₂ bb⟦ d ⟧a pA)

  codeBB : B → B → Type (lmax (lmax (lmax i j) k) l)
  codeBB b₀ b₁ = SetQuot (precodeBB-rel {b₀} {b₁})

  codeBA : B → A → Type (lmax (lmax (lmax i j) k) l)
  codeBA b₀ a₁ = SetQuot (precodeBA-rel {b₀} {a₁})

  c-bba : ∀ {a₀} d {a₁} (pc : codeBB a₀ (g (h d))) (pA : f (h d) =₀ a₁) → codeBA a₀ a₁
  c-bba d {a₁} c pA = SetQuot-rec SetQuot-is-set
    (λ pc → q[ pc-bba d pc pA ])
    (λ r → quot-rel $ pcBAr-cong r pA) c

  c-bab : ∀ {a₀} d {b₁} (pc : codeBA a₀ (f (h d))) (pB : g (h d) =₀ b₁) → codeBB a₀ b₁
  c-bab d {a₁} c pB = SetQuot-rec SetQuot-is-set
    (λ pc → q[ pc-bab d pc pB ])
    (λ r → quot-rel $ pcBBr-cong r pB) c

-- codeBP

  abstract
    pcBB-idp₀-idp₀-head : ∀ {d₀ b} (pB : g (h d₀) =₀ b)
      → q[ ⟧b idp₀ bb⟦ d₀ ⟧a idp₀ ba⟦ d₀ ⟧b pB ] == q[ ⟧b pB ] :> codeBB _ b
    pcBB-idp₀-idp₀-head {d₀} = Trunc-elim (λ _ → =-preserves-set SetQuot-is-set) lemma where
      lemma : ∀ {b} (pB : g (h d₀) == b)
        → q[ ⟧b idp₀ bb⟦ d₀ ⟧a idp₀ ba⟦ d₀ ⟧b [ pB ] ] == q[ ⟧b [ pB ] ] :> codeBB _ b
      lemma idp = quot-rel $ pcBBr-idp₀-idp₀ (⟧b idp₀)

  pcBA-prepend : ∀ {b₀} d₁ {b₂} → b₀ =₀ g (h d₁) → precodeBA (g (h d₁)) b₂ → precodeBA b₀ b₂
  pcBB-prepend : ∀ {b₀} d₁ {a₂} → b₀ =₀ g (h d₁) → precodeBB (g (h d₁)) a₂ → precodeBB b₀ a₂
  pcBA-prepend d₁ pB (pc-bba d pc pA) = pc-bba d (pcBB-prepend d₁ pB pc) pA
  pcBB-prepend d₁ pB (pc-b pB₁) = pc-bab d₁ (pc-bba d₁ (pc-b pB) idp₀) pB₁
  pcBB-prepend d₁ pB (pc-bab d pc pB₁) = pc-bab d (pcBA-prepend d₁ pB pc) pB₁

  abstract
    pcBA-prepend-idp₀ : ∀ {d₀ b₁} (pcBA : precodeBA (g (h d₀)) b₁)
      → q[ pcBA-prepend d₀ idp₀ pcBA ] == q[ pcBA ] :> codeBA (g (h d₀)) b₁
    pcBB-prepend-idp₀ : ∀ {d₀ a₁} (pcBB : precodeBB (g (h d₀)) a₁)
      → q[ pcBB-prepend d₀ idp₀ pcBB ] == q[ pcBB ] :> codeBB (g (h d₀)) a₁
    pcBA-prepend-idp₀ (pc-bba d pc pB) = pcBB-prepend-idp₀ pc |in-ctx λ c → c-bba d c pB
    pcBB-prepend-idp₀ (pc-b pB) = pcBB-idp₀-idp₀-head pB
    pcBB-prepend-idp₀ (pc-bab d pc pB) = pcBA-prepend-idp₀ pc |in-ctx λ c → c-bab d c pB

    transp-cBA-l : ∀ d {b₀ a₁} (p : g (h d) == b₀) (pcBA : precodeBA (g (h d)) a₁)
      → transport (λ x → codeBA x a₁) p q[ pcBA ] == q[ pcBA-prepend d [ ! p ] pcBA ]
    transp-cBA-l d idp pcBA = ! $ pcBA-prepend-idp₀ pcBA

    transp-cBB-l : ∀ d {b₀ b₁} (p : g (h d) == b₀) (pcBB : precodeBB (g (h d)) b₁)
      → transport (λ x → codeBB x b₁) p q[ pcBB ] == q[ pcBB-prepend d [ ! p ] pcBB ]
    transp-cBB-l d idp pcBB = ! $ pcBB-prepend-idp₀ pcBB

    transp-cBA-r : ∀ d {b₀ a₁} (p : f (h d) == a₁) (pcBA : precodeBA b₀ (f (h d)))
      → transport (λ x → codeBA b₀ x) p q[ pcBA ] == q[ pcBA ba⟦ d ⟧b idp₀ bb⟦ d ⟧a [ p ] ]
    transp-cBA-r d idp pcBA = ! $ quot-rel $ pcBAr-idp₀-idp₀ pcBA

    transp-cBB-r : ∀ d {b₀ b₁} (p : g (h d) == b₁) (pcBB : precodeBB b₀ (g (h d)))
      → transport (λ x → codeBB b₀ x) p q[ pcBB ] == q[ pcBB bb⟦ d ⟧a idp₀ ba⟦ d ⟧b [ p ] ]
    transp-cBB-r d idp pcBB = ! $ quot-rel $ pcBBr-idp₀-idp₀ pcBB

  module CodeBAEquivCodeBB (b₀ : B) where

    eqv-on-image : (d : D) → codeBA b₀ (f (h d)) ≃ codeBB b₀ (g (h d))
    eqv-on-image d = equiv to from to-from from-to where
      to = λ c → c-bab d c idp₀
      from = λ c → c-bba d c idp₀

      abstract
        from-to : ∀ cBA → from (to cBA) == cBA
        from-to = SetQuot-elim
          (λ _ → =-preserves-set SetQuot-is-set)
          (λ pcBA → quot-rel (pcBAr-idp₀-idp₀ pcBA))
          (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _))

        to-from : ∀ cBB → to (from cBB) == cBB
        to-from = SetQuot-elim
          (λ _ → =-preserves-set SetQuot-is-set)
          (λ pcBB → quot-rel (pcBBr-idp₀-idp₀ pcBB))
          (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _))

    abstract
      eqv-is-const : ∀ d₁ d₂ (p : h d₁ == h d₂)
        → eqv-on-image d₁ == eqv-on-image d₂
        [ (λ c → codeBA b₀ (f c) ≃ codeBB b₀ (g c)) ↓ p ]
      eqv-is-const d₁ d₂ p = ↓-Subtype-in (λ d → is-equiv-prop) $
        ↓-→-from-transp $ λ= $
          SetQuot-elim (λ _ → =-preserves-set SetQuot-is-set)
            (λ pcBA →
              transport (λ c → codeBB b₀ (g c)) p q[ pcBA ba⟦ d₁ ⟧b idp₀ ]
                =⟨ ap-∘ (codeBB b₀) g p |in-ctx (λ p → coe p q[ pcBA ba⟦ d₁ ⟧b idp₀ ]) ⟩
              transport (codeBB b₀) (ap g p) q[ pcBA ba⟦ d₁ ⟧b idp₀ ]
                =⟨ transp-cBB-r d₁ (ap g p) (pcBA ba⟦ d₁ ⟧b idp₀) ⟩
              q[ pcBA ba⟦ d₁ ⟧b idp₀ bb⟦ d₁ ⟧a idp₀ ba⟦ d₁ ⟧b [ ap g p ] ]
                =⟨ ! $ quot-rel $ pcBBr-switch (pcBA ba⟦ d₁ ⟧b idp₀) [ p ] ⟩
              q[ pcBA ba⟦ d₁ ⟧b idp₀ bb⟦ d₁ ⟧a [ ap f p ] ba⟦ d₂ ⟧b idp₀ ]
                =⟨ ! $ transp-cBA-r d₁ (ap f p) pcBA |in-ctx (λ c → c-bab d₂ c idp₀) ⟩
              c-bab d₂ (transport (codeBA b₀) (ap f p) q[ pcBA ]) idp₀
                =⟨ ∘-ap (codeBA b₀) f p |in-ctx (λ p → coe p q[ pcBA ]) |in-ctx (λ c → c-bab d₂ c idp₀) ⟩
              c-bab d₂ (transport (λ c → codeBA b₀ (f c)) p q[ pcBA ]) idp₀
                =∎)
            (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _))

    module SE = SurjExt
      (λ c → ≃-is-set SetQuot-is-set SetQuot-is-set)
      h h-is-surj
      eqv-on-image
      eqv-is-const

    abstract
      eqv : ∀ c → codeBA b₀ (f c) ≃ codeBB b₀ (g c)
      eqv = SE.ext

      eqv-β : ∀ d → eqv (h d) == eqv-on-image d
      eqv-β = SE.ext-β

  module CodeBP (b₀ : B) = PushoutRec (codeBA b₀) (codeBB b₀)
    (ua ∘ CodeBAEquivCodeBB.eqv b₀)

  codeBP : B → Pushout span → Type (lmax (lmax (lmax i j) k) l)
  codeBP = CodeBP.f

  abstract
    codeBP-level : ∀ {a₀ p₁} → is-set (codeBP a₀ p₁)
    codeBP-level {a₀} {p₁} = Pushout-elim
      {P = λ p₁ → is-set (codeBP a₀ p₁)}
      (λ a₁ → SetQuot-is-set)
      (λ b₁ → SetQuot-is-set)
      (λ c₁ → prop-has-all-paths-↓ is-set-is-prop)
      p₁
  codeBP-is-set = codeBP-level

  abstract
    transp-cBP-glue : ∀ {b₀} d₁ (pcBA : precodeBA b₀ (f (h d₁)))
      → transport (codeBP b₀) (glue (h d₁)) q[ pcBA ] == q[ pcBA ba⟦ d₁ ⟧b idp₀ ]
    transp-cBP-glue {b₀} d₁ pcBA =
      transport (codeBP b₀) (glue (h d₁)) q[ pcBA ]
        =⟨ ap (λ e → coe e q[ pcBA ]) (CodeBP.glue-β b₀ (h d₁) ∙ ap ua (CodeBAEquivCodeBB.eqv-β b₀ d₁)) ⟩
      coe (ua (CodeBAEquivCodeBB.eqv-on-image b₀ d₁)) q[ pcBA ]
        =⟨ coe-β (CodeBAEquivCodeBB.eqv-on-image b₀ d₁) q[ pcBA ] ⟩
      q[ pcBA ba⟦ d₁ ⟧b idp₀ ]
        =∎

    transp-cBP-!glue : ∀ {b₀} d₁ (pcBB : precodeBB b₀ (g (h d₁)))
      → transport (codeBP b₀) (! (glue (h d₁))) q[ pcBB ] == q[ pcBB bb⟦ d₁ ⟧a idp₀ ]
    transp-cBP-!glue {b₀} d₁ pcBB =
      transport (codeBP b₀) (! (glue (h d₁))) q[ pcBB ]
        =⟨ ap (λ e → coe e q[ pcBB ]) (ap-! (codeBP b₀) (glue (h d₁)))
         ∙ coe-! (ap (codeBP b₀) (glue (h d₁))) q[ pcBB ] ⟩
      transport! (codeBP b₀) (glue (h d₁)) q[ pcBB ]
        =⟨ ap (λ e → coe! e q[ pcBB ]) (CodeBP.glue-β b₀ (h d₁) ∙ ap ua (CodeBAEquivCodeBB.eqv-β b₀ d₁)) ⟩
      coe! (ua (CodeBAEquivCodeBB.eqv-on-image b₀ d₁)) q[ pcBB ]
        =⟨ coe!-β (CodeBAEquivCodeBB.eqv-on-image b₀ d₁) q[ pcBB ] ⟩
      q[ pcBB bb⟦ d₁ ⟧a idp₀ ]
        =∎

  -- code to path
  pcBA-to-path : ∀ {b₀ a₁} → precodeBA b₀ a₁ → right b₀ =₀ left a₁ :> Pushout span
  pcBB-to-path : ∀ {b₀ b₁} → precodeBB b₀ b₁ → right b₀ =₀ right b₁ :> Pushout span
  pcBA-to-path (pc-bba d pc pA) = pcBB-to-path pc ∙₀' !₀ [ glue (h d) ] ∙₀' ap₀ left pA
  pcBB-to-path (pc-b pB) = ap₀ right pB
  pcBB-to-path (pc-bab d pc pB) = pcBA-to-path pc ∙₀' [ glue (h d) ] ∙₀' ap₀ right pB

  abstract
    pcBA-to-path-rel : ∀ {b₀ a₁} {pcBA₀ pcBA₁ : precodeBA b₀ a₁}
      → precodeBA-rel pcBA₀ pcBA₁ → pcBA-to-path pcBA₀ == pcBA-to-path pcBA₁
    pcBB-to-path-rel : ∀ {b₀ b₁} {pcBB₀ pcBB₁ : precodeBB b₀ b₁}
      → precodeBB-rel pcBB₀ pcBB₁ → pcBB-to-path pcBB₀ == pcBB-to-path pcBB₁
    pcBA-to-path-rel (pcBAr-idp₀-idp₀ pcBA) =
        ∙₀'-assoc (pcBA-to-path pcBA) [ glue (h _) ] [ ! (glue (h _)) ]
      ∙ ap (λ p → pcBA-to-path pcBA ∙₀' [ p ]) (!-inv'-r (glue (h _)))
      ∙ ∙₀'-unit-r (pcBA-to-path pcBA)
    pcBA-to-path-rel (pcBAr-cong pcBB pA) = pcBB-to-path-rel pcBB |in-ctx _∙₀' !₀ [ glue (h _) ] ∙₀' ap₀ left pA
    pcBB-to-path-rel (pcBBr-idp₀-idp₀ pcBB) =
        ∙₀'-assoc (pcBB-to-path pcBB) [ ! (glue (h _)) ] [ glue (h _) ]
      ∙ ap (λ p → pcBB-to-path pcBB ∙₀' [ p ]) (!-inv'-l (glue (h _)))
      ∙ ∙₀'-unit-r (pcBB-to-path pcBB)
    pcBB-to-path-rel (pcBBr-switch pcBB pC) =
        ap (_∙₀' [ glue (h _) ]) (! (∙₀'-assoc (pcBB-to-path pcBB) [ ! (glue (h _)) ] (ap₀ left (ap₀ f pC))))
      ∙ ∙₀'-assoc (pcBB-to-path pcBB ∙₀' [ ! (glue (h _)) ]) (ap₀ left (ap₀ f pC)) [ glue (h _) ]
      ∙ ap ((pcBB-to-path pcBB ∙₀' [ ! (glue (h _)) ]) ∙₀'_) (natural₀ pC)
      where
        natural : ∀ {c₀ c₁} (p : c₀ == c₁)
          → (ap left (ap f p) ∙' glue c₁) == (glue c₀ ∙' ap right (ap g p))
          :> (left (f c₀) == right (g c₁) :> Pushout span)
        natural idp = ∙'-unit-l (glue _)

        natural₀ : ∀ {c₀ c₁} (p : c₀ =₀ c₁)
          → (ap₀ left (ap₀ f p) ∙₀' [ glue c₁ ]) == ([ glue c₀ ] ∙₀' ap₀ right (ap₀ g p))
          :> (left (f c₀) =₀ right (g c₁) :> Pushout span)
        natural₀ = Trunc-elim (λ _ → =-preserves-set Trunc-level) (ap [_] ∘ natural)
    pcBB-to-path-rel (pcBBr-cong pcBA pB) = pcBA-to-path-rel pcBA |in-ctx _∙₀' [ glue (h _) ] ∙₀' ap₀ right pB

  decodeBA : ∀ {b₀ a₁} → codeBA b₀ a₁ → right b₀ =₀ left a₁ :> Pushout span
  decodeBB : ∀ {b₀ b₁} → codeBB b₀ b₁ → right b₀ =₀ right b₁ :> Pushout span
  decodeBA = SetQuot-rec Trunc-level pcBA-to-path pcBA-to-path-rel
  decodeBB = SetQuot-rec Trunc-level pcBB-to-path pcBB-to-path-rel

  abstract
    decodeBA-is-decodeBB : ∀ {b₀} c₁ →
      decodeBA {b₀} {f c₁} == decodeBB {b₀} {g c₁}
      [ (λ p₁ → codeBP b₀ p₁ → right b₀ =₀ p₁) ↓ glue c₁ ]
    decodeBA-is-decodeBB {b₀ = b₀} = SurjExt.ext
      (λ _ → ↓-preserves-level $ Π-is-set λ _ → Trunc-level) h h-is-surj
      (λ d₁ → ↓-→-from-transp $ λ= $ SetQuot-elim
        {P = λ cBA → transport (right b₀ =₀_) (glue (h d₁)) (decodeBA cBA)
                  == decodeBB (transport (codeBP b₀) (glue (h d₁)) cBA)}
        (λ _ → =-preserves-set Trunc-level)
        (λ pcBA →
          transport (right b₀ =₀_) (glue (h d₁)) (pcBA-to-path pcBA)
            =⟨ transp₀-cst=₀idf [ glue (h d₁) ] (pcBA-to-path pcBA) ⟩
          pcBA-to-path pcBA ∙₀' [ glue (h d₁) ]
            =⟨ ! $ ap (λ e → decodeBB (–> e q[ pcBA ])) (CodeBAEquivCodeBB.eqv-β b₀ d₁) ⟩
          decodeBB (–> (CodeBAEquivCodeBB.eqv b₀ (h d₁)) q[ pcBA ])
            =⟨ ! $ ap decodeBB (coe-β (CodeBAEquivCodeBB.eqv b₀ (h d₁)) q[ pcBA ]) ⟩
          decodeBB (coe (ua (CodeBAEquivCodeBB.eqv b₀ (h d₁))) q[ pcBA ])
            =⟨ ! $ ap (λ p → decodeBB (coe p q[ pcBA ])) (CodeBP.glue-β b₀ (h d₁)) ⟩
          decodeBB (transport (codeBP b₀) (glue (h d₁)) q[ pcBA ])
            =∎)
        (λ _ → prop-has-all-paths-↓ $ Trunc-level {n = 0} _ _))
      (λ _ _ _ → prop-has-all-paths-↓ $ ↓-level $ Π-is-set λ _ → Trunc-level)

  decodeBP : ∀ {b₀ p₁} → codeBP b₀ p₁ → right b₀ =₀ p₁
  decodeBP {p₁ = p₁} = Pushout-elim
    (λ a₁ → decodeBA) (λ b₁ → decodeBB)
    decodeBA-is-decodeBB
    p₁
