open import HoTT
import homotopy.RelativelyConstantToSetExtendsViaSurjection as SurjExt

module homotopy.vankampen.CodeAP {i j k l}
  (span : Span {i} {j} {k})
  {D : Type l} (h : D → Span.C span) (h-is-surj : is-surj h) where

  open Span span

  data precodeAA (a₀ : A) : A → Type (lmax (lmax (lmax i j) k) l)
  data precodeAB (a₀ : A) (b₁ : B) : Type (lmax (lmax (lmax i j) k) l)

  data precodeAA a₀ where
    pc-a : ∀ {a₁} → a₀ =₀ a₁ → precodeAA a₀ a₁
    pc-aba : ∀ d {a₁} → precodeAB a₀ (g (h d)) → f (h d) =₀ a₁ → precodeAA a₀ a₁

  infix 65 pc-a
  syntax pc-a p = p⟧a p
  infixl 65 pc-aba
  syntax pc-aba d pcAB pA = pcAB ab⟦ d ⟧a pA

  data precodeAB a₀ b₁ where
    pc-aab : ∀ d → precodeAA a₀ (f (h d)) → g (h d) =₀ b₁ → precodeAB a₀ b₁

  infixl 65 pc-aab
  syntax pc-aab d pcAA pB = pcAA aa⟦ d ⟧b pB

  data precodeAA-rel {a₀ : A} : {a₁ : A}
    → precodeAA a₀ a₁ → precodeAA a₀ a₁ → Type (lmax (lmax (lmax i j) k) l)
  data precodeAB-rel {a₀ : A} : {b₁ : B}
    → precodeAB a₀ b₁ → precodeAB a₀ b₁ → Type (lmax (lmax (lmax i j) k) l)
  data precodeAA-rel {a₀} where
    pcAAr-idp₀-idp₀ : ∀ c pcAA → precodeAA-rel (pcAA aa⟦ c ⟧b idp₀ ab⟦ c ⟧a idp₀) pcAA
    pcAAr-cong : ∀ d {a₁ pcAB₁ pcAB₂} → precodeAB-rel pcAB₁ pcAB₂ → (pA : f (h d) =₀ a₁)
      → precodeAA-rel (pcAB₁ ab⟦ d ⟧a pA) (pcAB₂ ab⟦ d ⟧a pA)
  data precodeAB-rel {a₀} where
    pcABr-idp₀-idp₀ : ∀ d pcAB → precodeAB-rel (pcAB ab⟦ d ⟧a idp₀ aa⟦ d ⟧b idp₀) pcAB
    pcABr-switch : ∀ {d₀ d₁ : D} pcAB (pC : h d₀ =₀ h d₁)
      → precodeAB-rel (pcAB ab⟦ d₀ ⟧a ap₀ f pC aa⟦ d₁ ⟧b idp₀) (pcAB ab⟦ d₀ ⟧a idp₀ aa⟦ d₀ ⟧b ap₀ g pC)
    pcABr-cong : ∀ d {b₁ pcAA₁ pcAA₂} → precodeAA-rel pcAA₁ pcAA₂ → (pB : g (h d) =₀ b₁)
      → precodeAB-rel (pcAA₁ aa⟦ d ⟧b pB) (pcAA₂ aa⟦ d ⟧b pB)

  codeAA : A → A → Type (lmax (lmax (lmax i j) k) l)
  codeAA a₀ a₁ = SetQuot (precodeAA-rel {a₀} {a₁})

  codeAB : A → B → Type (lmax (lmax (lmax i j) k) l)
  codeAB a₀ b₁ = SetQuot (precodeAB-rel {a₀} {b₁})

-- codeAP

  transp-cAB-r : {a₀ : A} (d : D) (pcAB : precodeAB a₀ (g (h d))) {b₁ : B} (p : g (h d) == b₁)
    → transport (λ x → codeAB a₀ x) p q[ pcAB ] == q[ pcAB ab⟦ d ⟧a idp₀ aa⟦ d ⟧b [ p ] ]
  transp-cAB-r d pcAB idp = ! $ quot-rel $ pcABr-idp₀-idp₀ d pcAB

  transp-cAA-r : {a₀ : A} (d : D) (pcAA : precodeAA a₀ (f (h d))) {a₁ : A} (p : f (h d) == a₁)
    → transport (λ x → codeAA a₀ x) p q[ pcAA ] == q[ pcAA aa⟦ d ⟧b idp₀ ab⟦ d ⟧a [ p ] ]
  transp-cAA-r d pcAA idp = ! $ quot-rel $ pcAAr-idp₀-idp₀ d pcAA

  module CodeAAEquivCodeAB (a₀ : A) where

    eqv-on-image : (d : D) → codeAA a₀ (f (h d)) ≃ codeAB a₀ (g (h d))
    eqv-on-image d = equiv to from to-from from-to where
      to : codeAA a₀ (f (h d)) → codeAB a₀ (g (h d))
      to = SetQuot-rec SetQuot-is-set
        (λ pcAA → q[ pcAA aa⟦ d ⟧b idp₀ ])
        (λ r → quot-rel $ pcABr-cong d r idp₀)

      from : codeAB a₀ (g (h d)) → codeAA a₀ (f (h d))
      from = SetQuot-rec SetQuot-is-set
        (λ pcAB → q[ pcAB ab⟦ d ⟧a idp₀ ])
        (λ r → quot-rel $ pcAAr-cong d r idp₀)

      from-to : ∀ cAA → from (to cAA) == cAA
      from-to = SetQuot-elim
        (λ _ → =-preserves-set SetQuot-is-set)
        (λ pcAA → quot-rel (pcAAr-idp₀-idp₀ d pcAA))
        (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _))

      to-from : ∀ cAB → to (from cAB) == cAB
      to-from = SetQuot-elim
        (λ _ → =-preserves-set SetQuot-is-set)
        (λ pcAB → quot-rel (pcABr-idp₀-idp₀ d pcAB))
        (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _))

    eqv-is-const : ∀ d₁ d₂ → (p : h d₁ == h d₂)
      → eqv-on-image d₁ == eqv-on-image d₂
      [ (λ c → codeAA a₀ (f c) ≃ codeAB a₀ (g c)) ↓ p ]
    eqv-is-const d₁ d₂ p = ↓-Subtype-in (λ d → is-equiv-prop) $
      ↓-→-from-transp $ λ= $
        SetQuot-elim (λ _ → =-preserves-set SetQuot-is-set)
          (λ pcAA →
            transport (λ c → codeAB a₀ (g c)) p q[ pcAA aa⟦ d₁ ⟧b idp₀ ]
              =⟨ ap-∘ (codeAB a₀) g p |in-ctx (λ p → coe p q[ pcAA aa⟦ d₁ ⟧b idp₀ ]) ⟩
            transport (codeAB a₀) (ap g p) q[ pcAA aa⟦ d₁ ⟧b idp₀ ]
              =⟨ transp-cAB-r d₁ (pcAA aa⟦ d₁ ⟧b idp₀) (ap g p) ⟩
            q[ pcAA aa⟦ d₁ ⟧b idp₀ ab⟦ d₁ ⟧a idp₀ aa⟦ d₁ ⟧b [ ap g p ] ]
              =⟨ ! $ quot-rel $ pcABr-switch (pcAA aa⟦ d₁ ⟧b idp₀) [ p ] ⟩
            q[ pcAA aa⟦ d₁ ⟧b idp₀ ab⟦ d₁ ⟧a [ ap f p ] aa⟦ d₂ ⟧b idp₀ ]
              =⟨ ! $ transp-cAA-r d₁ pcAA (ap f p) |in-ctx –> (eqv-on-image d₂) ⟩
            –> (eqv-on-image d₂) (transport (codeAA a₀) (ap f p) q[ pcAA ])
              =⟨ ∘-ap (codeAA a₀) f p |in-ctx (λ p → coe p q[ pcAA ]) |in-ctx –> (eqv-on-image d₂) ⟩
            –> (eqv-on-image d₂) (transport (λ c → codeAA a₀ (f c)) p q[ pcAA ])
              =∎)
          (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _))

    module SE = SurjExt
      (λ c → ≃-is-set SetQuot-is-set SetQuot-is-set)
      h h-is-surj
      eqv-on-image
      eqv-is-const

    eqv : ∀ c → codeAA a₀ (f c) ≃ codeAB a₀ (g c)
    eqv = SE.surj-ext

    eqv-β : ∀ d → eqv (h d) == eqv-on-image d
    eqv-β = SE.surj-ext-β

  codeAP : A → Pushout span → Type (lmax (lmax (lmax i j) k) l)
  codeAP a₀ = Pushout-rec (codeAA a₀) (codeAB a₀)
    (ua ∘ CodeAAEquivCodeAB.eqv a₀)
