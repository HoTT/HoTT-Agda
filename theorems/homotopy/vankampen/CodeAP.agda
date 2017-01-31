{-# OPTIONS --without-K --rewriting #-}

{- Remember to keep CodeBP.agda in sync. -}

open import HoTT
import homotopy.RelativelyConstantToSetExtendsViaSurjection as SurjExt

module homotopy.vankampen.CodeAP {i j k l}
  (span : Span {i} {j} {k})
  {D : Type l} (h : D → Span.C span) (h-is-surj : is-surj h) where

  open Span span

  data precodeAA (a₀ : A) : A → Type (lmax (lmax (lmax i j) k) l)
  data precodeAB (a₀ : A) (b₁ : B) : Type (lmax (lmax (lmax i j) k) l)

  data precodeAA a₀ where
    pc-a : ∀ {a₁} (pA : a₀ =₀ a₁) → precodeAA a₀ a₁
    pc-aba : ∀ d {a₁} (pc : precodeAB a₀ (g (h d))) (pA : f (h d) =₀ a₁) → precodeAA a₀ a₁

  infix 66 pc-a
  syntax pc-a p = ⟧a p
  infixl 65 pc-aba
  syntax pc-aba d pcAB pA = pcAB ab⟦ d ⟧a pA

  data precodeAB a₀ b₁ where
    pc-aab : ∀ d (pc : precodeAA a₀ (f (h d))) (pB : g (h d) =₀ b₁) → precodeAB a₀ b₁

  infixl 65 pc-aab
  syntax pc-aab d pcAA pB = pcAA aa⟦ d ⟧b pB

  data precodeAA-rel {a₀ : A} : {a₁ : A}
    → precodeAA a₀ a₁ → precodeAA a₀ a₁ → Type (lmax (lmax (lmax i j) k) l)
  data precodeAB-rel {a₀ : A} : {b₁ : B}
    → precodeAB a₀ b₁ → precodeAB a₀ b₁ → Type (lmax (lmax (lmax i j) k) l)
  data precodeAA-rel {a₀} where
    pcAAr-idp₀-idp₀ : ∀ {d} pcAA → precodeAA-rel (pcAA aa⟦ d ⟧b idp₀ ab⟦ d ⟧a idp₀) pcAA
    pcAAr-cong : ∀ {d a₁ pcAB₁ pcAB₂} (r : precodeAB-rel pcAB₁ pcAB₂) (pA : f (h d) =₀ a₁)
      → precodeAA-rel (pcAB₁ ab⟦ d ⟧a pA) (pcAB₂ ab⟦ d ⟧a pA)
  data precodeAB-rel {a₀} where
    pcABr-idp₀-idp₀ : ∀ {d} pcAB → precodeAB-rel (pcAB ab⟦ d ⟧a idp₀ aa⟦ d ⟧b idp₀) pcAB
    pcABr-switch : ∀ {d₀ d₁ : D} pcAB (pC : h d₀ =₀ h d₁)
      → precodeAB-rel (pcAB ab⟦ d₀ ⟧a ap₀ f pC aa⟦ d₁ ⟧b idp₀) (pcAB ab⟦ d₀ ⟧a idp₀ aa⟦ d₀ ⟧b ap₀ g pC)
    pcABr-cong : ∀ {d b₁ pcAA₁ pcAA₂} (r : precodeAA-rel pcAA₁ pcAA₂) (pB : g (h d) =₀ b₁)
      → precodeAB-rel (pcAA₁ aa⟦ d ⟧b pB) (pcAA₂ aa⟦ d ⟧b pB)

  codeAA : A → A → Type (lmax (lmax (lmax i j) k) l)
  codeAA a₀ a₁ = SetQuot (precodeAA-rel {a₀} {a₁})

  codeAB : A → B → Type (lmax (lmax (lmax i j) k) l)
  codeAB a₀ b₁ = SetQuot (precodeAB-rel {a₀} {b₁})

  c-aba : ∀ {a₀} d {a₁} (pc : codeAB a₀ (g (h d))) (pA : f (h d) =₀ a₁) → codeAA a₀ a₁
  c-aba d {a₁} c pA = SetQuot-rec SetQuot-is-set
    (λ pc → q[ pc-aba d pc pA ])
    (λ r → quot-rel $ pcAAr-cong r pA) c

  c-aab : ∀ {a₀} d {b₁} (pc : codeAA a₀ (f (h d))) (pB : g (h d) =₀ b₁) → codeAB a₀ b₁
  c-aab d {a₁} c pB = SetQuot-rec SetQuot-is-set
    (λ pc → q[ pc-aab d pc pB ])
    (λ r → quot-rel $ pcABr-cong r pB) c

-- codeAP

  abstract
    pcAA-idp₀-idp₀-head : ∀ {d₀ a} (pA : f (h d₀) =₀ a)
      → q[ ⟧a idp₀ aa⟦ d₀ ⟧b idp₀ ab⟦ d₀ ⟧a pA ] == q[ ⟧a pA ] :> codeAA _ a
    pcAA-idp₀-idp₀-head {d₀} = Trunc-elim (λ _ → =-preserves-set SetQuot-is-set) lemma where
      lemma : ∀ {a} (pA : f (h d₀) == a)
        → q[ ⟧a idp₀ aa⟦ d₀ ⟧b idp₀ ab⟦ d₀ ⟧a [ pA ] ] == q[ ⟧a [ pA ] ] :> codeAA _ a
      lemma idp = quot-rel $ pcAAr-idp₀-idp₀ (⟧a idp₀)

  pcAA-prepend : ∀ {a₀} d₁ {a₂} → a₀ =₀ f (h d₁) → precodeAA (f (h d₁)) a₂ → precodeAA a₀ a₂
  pcAB-prepend : ∀ {a₀} d₁ {b₂} → a₀ =₀ f (h d₁) → precodeAB (f (h d₁)) b₂ → precodeAB a₀ b₂
  pcAA-prepend d₁ pA (pc-a pA₁) = pc-aba d₁ (pc-aab d₁ (pc-a pA) idp₀) pA₁
  pcAA-prepend d₁ pA (pc-aba d pc pA₁) = pc-aba d (pcAB-prepend d₁ pA pc) pA₁
  pcAB-prepend d₁ pA (pc-aab d pc pB) = pc-aab d (pcAA-prepend d₁ pA pc) pB

  abstract
    pcAA-prepend-idp₀ : ∀ {d₀ a₁} (pcAA : precodeAA (f (h d₀)) a₁)
      → q[ pcAA-prepend d₀ idp₀ pcAA ] == q[ pcAA ] :> codeAA (f (h d₀)) a₁
    pcAB-prepend-idp₀ : ∀ {d₀ b₁} (pcAB : precodeAB (f (h d₀)) b₁)
      → q[ pcAB-prepend d₀ idp₀ pcAB ] == q[ pcAB ] :> codeAB (f (h d₀)) b₁
    pcAA-prepend-idp₀ (pc-a pA) = pcAA-idp₀-idp₀-head pA
    pcAA-prepend-idp₀ (pc-aba d pc pA) = pcAB-prepend-idp₀ pc |in-ctx λ c → c-aba d c pA
    pcAB-prepend-idp₀ (pc-aab d pc pA) = pcAA-prepend-idp₀ pc |in-ctx λ c → c-aab d c pA

    transp-cAA-l : ∀ d {a₀ a₁} (p : f (h d) == a₀) (pcAA : precodeAA (f (h d)) a₁)
      → transport (λ x → codeAA x a₁) p q[ pcAA ] == q[ pcAA-prepend d [ ! p ] pcAA ]
    transp-cAA-l d idp pcAA = ! $ pcAA-prepend-idp₀ pcAA

    transp-cAB-l : ∀ d {a₀ b₁} (p : f (h d) == a₀) (pcAB : precodeAB (f (h d)) b₁)
      → transport (λ x → codeAB x b₁) p q[ pcAB ] == q[ pcAB-prepend d [ ! p ] pcAB ]
    transp-cAB-l d idp pcAB = ! $ pcAB-prepend-idp₀ pcAB

    transp-cAA-r : ∀ d {a₀ a₁} (p : f (h d) == a₁) (pcAA : precodeAA a₀ (f (h d)))
      → transport (λ x → codeAA a₀ x) p q[ pcAA ] == q[ pcAA aa⟦ d ⟧b idp₀ ab⟦ d ⟧a [ p ] ]
    transp-cAA-r d idp pcAA = ! $ quot-rel $ pcAAr-idp₀-idp₀ pcAA

    transp-cAB-r : ∀ d {a₀ b₁} (p : g (h d) == b₁) (pcAB : precodeAB a₀ (g (h d)))
      → transport (λ x → codeAB a₀ x) p q[ pcAB ] == q[ pcAB ab⟦ d ⟧a idp₀ aa⟦ d ⟧b [ p ] ]
    transp-cAB-r d idp pcAB = ! $ quot-rel $ pcABr-idp₀-idp₀ pcAB

  module CodeAAEquivCodeAB (a₀ : A) where

    eqv-on-image : (d : D) → codeAA a₀ (f (h d)) ≃ codeAB a₀ (g (h d))
    eqv-on-image d = equiv to from to-from from-to where
      to = λ c → c-aab d c idp₀
      from = λ c → c-aba d c idp₀

      abstract
        from-to : ∀ cAA → from (to cAA) == cAA
        from-to = SetQuot-elim
          (λ _ → =-preserves-set SetQuot-is-set)
          (λ pcAA → quot-rel (pcAAr-idp₀-idp₀ pcAA))
          (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _))

        to-from : ∀ cAB → to (from cAB) == cAB
        to-from = SetQuot-elim
          (λ _ → =-preserves-set SetQuot-is-set)
          (λ pcAB → quot-rel (pcABr-idp₀-idp₀ pcAB))
          (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _))

    abstract
      eqv-is-const : ∀ d₁ d₂ (p : h d₁ == h d₂)
        → eqv-on-image d₁ == eqv-on-image d₂
        [ (λ c → codeAA a₀ (f c) ≃ codeAB a₀ (g c)) ↓ p ]
      eqv-is-const d₁ d₂ p = ↓-Subtype-in (λ d → is-equiv-prop) $
        ↓-→-from-transp $ λ= $
          SetQuot-elim (λ _ → =-preserves-set SetQuot-is-set)
            (λ pcAA →
              transport (λ c → codeAB a₀ (g c)) p q[ pcAA aa⟦ d₁ ⟧b idp₀ ]
                =⟨ ap-∘ (codeAB a₀) g p |in-ctx (λ p → coe p q[ pcAA aa⟦ d₁ ⟧b idp₀ ]) ⟩
              transport (codeAB a₀) (ap g p) q[ pcAA aa⟦ d₁ ⟧b idp₀ ]
                =⟨ transp-cAB-r d₁ (ap g p) (pcAA aa⟦ d₁ ⟧b idp₀) ⟩
              q[ pcAA aa⟦ d₁ ⟧b idp₀ ab⟦ d₁ ⟧a idp₀ aa⟦ d₁ ⟧b [ ap g p ] ]
                =⟨ ! $ quot-rel $ pcABr-switch (pcAA aa⟦ d₁ ⟧b idp₀) [ p ] ⟩
              q[ pcAA aa⟦ d₁ ⟧b idp₀ ab⟦ d₁ ⟧a [ ap f p ] aa⟦ d₂ ⟧b idp₀ ]
                =⟨ ! $ transp-cAA-r d₁ (ap f p) pcAA |in-ctx (λ c → c-aab d₂ c idp₀) ⟩
              c-aab d₂ (transport (codeAA a₀) (ap f p) q[ pcAA ]) idp₀
                =⟨ ∘-ap (codeAA a₀) f p |in-ctx (λ p → coe p q[ pcAA ]) |in-ctx (λ c → c-aab d₂ c idp₀) ⟩
              c-aab d₂ (transport (λ c → codeAA a₀ (f c)) p q[ pcAA ]) idp₀
                =∎)
            (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _))

    module SE = SurjExt
      (λ c → ≃-is-set SetQuot-is-set SetQuot-is-set)
      h h-is-surj
      eqv-on-image
      eqv-is-const

    abstract
      eqv : ∀ c → codeAA a₀ (f c) ≃ codeAB a₀ (g c)
      eqv = SE.surj-ext

      eqv-β : ∀ d → eqv (h d) == eqv-on-image d
      eqv-β = SE.surj-ext-β

  module CodeAP (a₀ : A) = PushoutRec (codeAA a₀) (codeAB a₀)
    (ua ∘ CodeAAEquivCodeAB.eqv a₀)

  codeAP : A → Pushout span → Type (lmax (lmax (lmax i j) k) l)
  codeAP = CodeAP.f

  abstract
    codeAP-level : ∀ {a₀ p₁} → is-set (codeAP a₀ p₁)
    codeAP-level {a₀} {p₁} = Pushout-elim
      {P = λ p₁ → is-set (codeAP a₀ p₁)}
      (λ a₁ → SetQuot-is-set)
      (λ b₁ → SetQuot-is-set)
      (λ c₁ → prop-has-all-paths-↓ is-set-is-prop)
      p₁
  codeAP-is-set = codeAP-level

  abstract
    transp-cAP-glue : ∀ {a₀} d₁ (pcAA : precodeAA a₀ (f (h d₁)))
      → transport (codeAP a₀) (glue (h d₁)) q[ pcAA ] == q[ pcAA aa⟦ d₁ ⟧b idp₀ ]
    transp-cAP-glue {a₀} d₁ pcAA =
      transport (codeAP a₀) (glue (h d₁)) q[ pcAA ]
        =⟨ ap (λ e → coe e q[ pcAA ]) (CodeAP.glue-β a₀ (h d₁) ∙ ap ua (CodeAAEquivCodeAB.eqv-β a₀ d₁)) ⟩
      coe (ua (CodeAAEquivCodeAB.eqv-on-image a₀ d₁)) q[ pcAA ]
        =⟨ coe-β (CodeAAEquivCodeAB.eqv-on-image a₀ d₁) q[ pcAA ] ⟩
      q[ pcAA aa⟦ d₁ ⟧b idp₀ ]
        =∎

    transp-cAP-!glue : ∀ {a₀} d₁ (pcAB : precodeAB a₀ (g (h d₁)))
      → transport (codeAP a₀) (! (glue (h d₁))) q[ pcAB ] == q[ pcAB ab⟦ d₁ ⟧a idp₀ ]
    transp-cAP-!glue {a₀} d₁ pcAB =
      transport (codeAP a₀) (! (glue (h d₁))) q[ pcAB ]
        =⟨ ap (λ e → coe e q[ pcAB ]) (ap-! (codeAP a₀) (glue (h d₁)))
         ∙ coe-! (ap (codeAP a₀) (glue (h d₁))) q[ pcAB ] ⟩
      transport! (codeAP a₀) (glue (h d₁)) q[ pcAB ]
        =⟨ ap (λ e → coe! e q[ pcAB ]) (CodeAP.glue-β a₀ (h d₁) ∙ ap ua (CodeAAEquivCodeAB.eqv-β a₀ d₁)) ⟩
      coe! (ua (CodeAAEquivCodeAB.eqv-on-image a₀ d₁)) q[ pcAB ]
        =⟨ coe!-β (CodeAAEquivCodeAB.eqv-on-image a₀ d₁) q[ pcAB ] ⟩
      q[ pcAB ab⟦ d₁ ⟧a idp₀ ]
        =∎

  -- code to path
  pcAA-to-path : ∀ {a₀ a₁} → precodeAA a₀ a₁ → left a₀ =₀ left a₁ :> Pushout span
  pcAB-to-path : ∀ {a₀ b₁} → precodeAB a₀ b₁ → left a₀ =₀ right b₁ :> Pushout span
  pcAA-to-path (pc-a pA) = ap₀ left pA
  pcAA-to-path (pc-aba d pc pA) = pcAB-to-path pc ∙₀' !₀ [ glue (h d) ] ∙₀' ap₀ left pA
  pcAB-to-path (pc-aab d pc pB) = pcAA-to-path pc ∙₀' [ glue (h d) ] ∙₀' ap₀ right pB

  abstract
    pcAA-to-path-rel : ∀ {a₀ a₁} {pcAA₀ pcAA₁ : precodeAA a₀ a₁}
      → precodeAA-rel pcAA₀ pcAA₁ → pcAA-to-path pcAA₀ == pcAA-to-path pcAA₁
    pcAB-to-path-rel : ∀ {a₀ b₁} {pcAB₀ pcAB₁ : precodeAB a₀ b₁}
      → precodeAB-rel pcAB₀ pcAB₁ → pcAB-to-path pcAB₀ == pcAB-to-path pcAB₁
    pcAA-to-path-rel (pcAAr-idp₀-idp₀ pcAA) =
        ∙₀'-assoc (pcAA-to-path pcAA) [ glue (h _) ] [ ! (glue (h _)) ]
      ∙ ap (λ p → pcAA-to-path pcAA ∙₀' [ p ]) (!-inv'-r (glue (h _)))
      ∙ ∙₀'-unit-r (pcAA-to-path pcAA)
    pcAA-to-path-rel (pcAAr-cong pcAB pA) = pcAB-to-path-rel pcAB |in-ctx _∙₀' !₀ [ glue (h _) ] ∙₀' ap₀ left pA
    pcAB-to-path-rel (pcABr-idp₀-idp₀ pcAB) =
        ∙₀'-assoc (pcAB-to-path pcAB) [ ! (glue (h _)) ] [ glue (h _) ]
      ∙ ap (λ p → pcAB-to-path pcAB ∙₀' [ p ]) (!-inv'-l (glue (h _)))
      ∙ ∙₀'-unit-r (pcAB-to-path pcAB)
    pcAB-to-path-rel (pcABr-switch pcAB pC) =
        ap (_∙₀' [ glue (h _) ]) (! (∙₀'-assoc (pcAB-to-path pcAB) [ ! (glue (h _)) ] (ap₀ left (ap₀ f pC))))
      ∙ ∙₀'-assoc (pcAB-to-path pcAB ∙₀' [ ! (glue (h _)) ]) (ap₀ left (ap₀ f pC)) [ glue (h _) ]
      ∙ ap ((pcAB-to-path pcAB ∙₀' [ ! (glue (h _)) ]) ∙₀'_) (natural₀ pC)
      where
        natural : ∀ {c₀ c₁} (p : c₀ == c₁)
          → (ap left (ap f p) ∙' glue c₁) == (glue c₀ ∙' ap right (ap g p))
          :> (left (f c₀) == right (g c₁) :> Pushout span)
        natural idp = ∙'-unit-l (glue _)

        natural₀ : ∀ {c₀ c₁} (p : c₀ =₀ c₁)
          → (ap₀ left (ap₀ f p) ∙₀' [ glue c₁ ]) == ([ glue c₀ ] ∙₀' ap₀ right (ap₀ g p))
          :> (left (f c₀) =₀ right (g c₁) :> Pushout span)
        natural₀ = Trunc-elim (λ _ → =-preserves-set Trunc-level) (ap [_] ∘ natural)
    pcAB-to-path-rel (pcABr-cong pcAA pB) = pcAA-to-path-rel pcAA |in-ctx _∙₀' [ glue (h _) ] ∙₀' ap₀ right pB

  decodeAA : ∀ {a₀ a₁} → codeAA a₀ a₁ → left a₀ =₀ left a₁ :> Pushout span
  decodeAB : ∀ {a₀ b₁} → codeAB a₀ b₁ → left a₀ =₀ right b₁ :> Pushout span
  decodeAA = SetQuot-rec Trunc-level pcAA-to-path pcAA-to-path-rel
  decodeAB = SetQuot-rec Trunc-level pcAB-to-path pcAB-to-path-rel

  abstract
    decodeAA-is-decodeAB : ∀ {a₀} c₁ →
      decodeAA {a₀} {f c₁} == decodeAB {a₀} {g c₁}
      [ (λ p₁ → codeAP a₀ p₁ → left a₀ =₀ p₁) ↓ glue c₁ ]
    decodeAA-is-decodeAB {a₀ = a₀} = SurjExt.surj-ext
      (λ _ → ↓-preserves-level $ Π-is-set λ _ → Trunc-level) h h-is-surj
      (λ d₁ → ↓-→-from-transp $ λ= $ SetQuot-elim
        {P = λ cAA → transport (left a₀ =₀_) (glue (h d₁)) (decodeAA cAA)
                  == decodeAB (transport (codeAP a₀) (glue (h d₁)) cAA)}
        (λ _ → =-preserves-set Trunc-level)
        (λ pcAA →
          transport (left a₀ =₀_) (glue (h d₁)) (pcAA-to-path pcAA)
            =⟨ transp₀-cst=₀idf [ glue (h d₁) ] (pcAA-to-path pcAA) ⟩
          pcAA-to-path pcAA ∙₀' [ glue (h d₁) ]
            =⟨ ! $ ap (λ e → decodeAB (–> e q[ pcAA ])) (CodeAAEquivCodeAB.eqv-β a₀ d₁) ⟩
          decodeAB (–> (CodeAAEquivCodeAB.eqv a₀ (h d₁)) q[ pcAA ])
            =⟨ ! $ ap decodeAB (coe-β (CodeAAEquivCodeAB.eqv a₀ (h d₁)) q[ pcAA ]) ⟩
          decodeAB (coe (ua (CodeAAEquivCodeAB.eqv a₀ (h d₁))) q[ pcAA ])
            =⟨ ! $ ap (λ p → decodeAB (coe p q[ pcAA ])) (CodeAP.glue-β a₀ (h d₁)) ⟩
          decodeAB (transport (codeAP a₀) (glue (h d₁)) q[ pcAA ])
            =∎)
        (λ _ → prop-has-all-paths-↓ $ Trunc-level {n = 0} _ _))
      (λ _ _ _ → prop-has-all-paths-↓ $ ↓-level $ Π-is-set λ _ → Trunc-level)

  decodeAP : ∀ {a₀ p₁} → codeAP a₀ p₁ → left a₀ =₀ p₁
  decodeAP {p₁ = p₁} = Pushout-elim
    (λ a₁ → decodeAA) (λ b₁ → decodeAB)
    decodeAA-is-decodeAB
    p₁
