{-# OPTIONS --without-K --rewriting #-}

open import HoTT
import homotopy.RelativelyConstantToSetExtendsViaSurjection as SurjExt

module homotopy.vankampen.CodeBP {i j k l}
  (span : Span {i} {j} {k})
  {D : Type l} (h : D → Span.C span) (h-is-surj : is-surj h) where

  open Span span

  data precodeBB (b₀ : B) : B → Type (lmax (lmax (lmax i j) k) l)
  data precodeBA (b₀ : B) (a₁ : A) : Type (lmax (lmax (lmax i j) k) l)

  data precodeBB b₀ where
    pc-b : ∀ {b₁} → b₀ =₀ b₁ → precodeBB b₀ b₁
    pc-aba : ∀ d {b₁} → precodeBA b₀ (f (h d)) → g (h d) =₀ b₁ → precodeBB b₀ b₁

  infix 65 pc-b
  syntax pc-b p = p⟧b p
  infixl 65 pc-aba
  syntax pc-aba d pcBA pB = pcBA ba⟦ d ⟧b pB

  data precodeBA b₀ a₁ where
    pc-aab : ∀ d → precodeBB b₀ (g (h d)) → f (h d) =₀ a₁ → precodeBA b₀ a₁

  infixl 65 pc-aab
  syntax pc-aab d pcBB pA = pcBB bb⟦ d ⟧a pA

  data precodeBB-rel {b₀ : B} : {b₁ : B}
    → precodeBB b₀ b₁ → precodeBB b₀ b₁ → Type (lmax (lmax (lmax i j) k) l)
  data precodeBA-rel {b₀ : B} : {a₁ : A}
    → precodeBA b₀ a₁ → precodeBA b₀ a₁ → Type (lmax (lmax (lmax i j) k) l)
  data precodeBB-rel {b₀} where
    pcBBr-idp₀-idp₀ : ∀ c pcBB → precodeBB-rel (pcBB bb⟦ c ⟧a idp₀ ba⟦ c ⟧b idp₀) pcBB
    pcBBr-switch : ∀ {d₀ d₁ : D} pcBB (pC : h d₀ =₀ h d₁)
      → precodeBB-rel (pcBB bb⟦ d₀ ⟧a ap₀ f pC ba⟦ d₁ ⟧b idp₀) (pcBB bb⟦ d₀ ⟧a idp₀ ba⟦ d₀ ⟧b ap₀ g pC)
    pcBBr-cong : ∀ d {b₁ pcBA₁ pcBA₂} → precodeBA-rel pcBA₁ pcBA₂ → (pB : g (h d) =₀ b₁)
      → precodeBB-rel (pcBA₁ ba⟦ d ⟧b pB) (pcBA₂ ba⟦ d ⟧b pB)
  data precodeBA-rel {b₀} where
    pcBAr-idp₀-idp₀ : ∀ d pcBA → precodeBA-rel (pcBA ba⟦ d ⟧b idp₀ bb⟦ d ⟧a idp₀) pcBA
    pcBAr-cong : ∀ d {a₁ pcBB₁ pcBB₂} → precodeBB-rel pcBB₁ pcBB₂ → (pA : f (h d) =₀ a₁)
      → precodeBA-rel (pcBB₁ bb⟦ d ⟧a pA) (pcBB₂ bb⟦ d ⟧a pA)

  codeBB : B → B → Type (lmax (lmax (lmax i j) k) l)
  codeBB b₀ b₁ = SetQuot (precodeBB-rel {b₀} {b₁})

  codeBA : B → A → Type (lmax (lmax (lmax i j) k) l)
  codeBA b₀ a₁ = SetQuot (precodeBA-rel {b₀} {a₁})

-- codeBP

  transp-cBA-r : {b₀ : B} (d : D) (pcBA : precodeBA b₀ (f (h d))) {a₁ : A} (p : f (h d) == a₁)
    → transport (λ x → codeBA b₀ x) p q[ pcBA ] == q[ pcBA ba⟦ d ⟧b idp₀ bb⟦ d ⟧a [ p ] ]
  transp-cBA-r d pcBA idp = ! $ quot-rel $ pcBAr-idp₀-idp₀ d pcBA

  transp-cBB-r : {b₀ : B} (d : D) (pcBB : precodeBB b₀ (g (h d))) {b₁ : B} (p : g (h d) == b₁)
    → transport (λ x → codeBB b₀ x) p q[ pcBB ] == q[ pcBB bb⟦ d ⟧a idp₀ ba⟦ d ⟧b [ p ] ]
  transp-cBB-r d pcBB idp = ! $ quot-rel $ pcBBr-idp₀-idp₀ d pcBB

  module CodeBAEquivCodeBB (b₀ : B) where

    eqv-on-image : (d : D) → codeBA b₀ (f (h d)) ≃ codeBB b₀ (g (h d))
    eqv-on-image d = equiv to from to-from from-to where
      to : codeBA b₀ (f (h d)) → codeBB b₀ (g (h d))
      to = SetQuot-rec SetQuot-is-set
        (λ pcBA → q[ pcBA ba⟦ d ⟧b idp₀ ])
        (λ r → quot-rel $ pcBBr-cong d r idp₀)

      from : codeBB b₀ (g (h d)) → codeBA b₀ (f (h d))
      from = SetQuot-rec SetQuot-is-set
        (λ pcBB → q[ pcBB bb⟦ d ⟧a idp₀ ])
        (λ r → quot-rel $ pcBAr-cong d r idp₀)

      from-to : ∀ cBA → from (to cBA) == cBA
      from-to = SetQuot-elim
        (λ _ → =-preserves-set SetQuot-is-set)
        (λ pcBA → quot-rel (pcBAr-idp₀-idp₀ d pcBA))
        (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _))

      to-from : ∀ cBB → to (from cBB) == cBB
      to-from = SetQuot-elim
        (λ _ → =-preserves-set SetQuot-is-set)
        (λ pcBB → quot-rel (pcBBr-idp₀-idp₀ d pcBB))
        (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _))

    eqv-is-const : ∀ d₁ d₂ → (p : h d₁ == h d₂)
      → eqv-on-image d₁ == eqv-on-image d₂
      [ (λ c → codeBA b₀ (f c) ≃ codeBB b₀ (g c)) ↓ p ]
    eqv-is-const d₁ d₂ p = ↓-Subtype-in (λ d → is-equiv-prop) $
      ↓-→-from-transp $ λ= $
        SetQuot-elim (λ _ → =-preserves-set SetQuot-is-set)
          (λ pcBA →
            transport (λ c → codeBB b₀ (g c)) p q[ pcBA ba⟦ d₁ ⟧b idp₀ ]
              =⟨ ap-∘ (codeBB b₀) g p |in-ctx (λ p → coe p q[ pcBA ba⟦ d₁ ⟧b idp₀ ]) ⟩
            transport (codeBB b₀) (ap g p) q[ pcBA ba⟦ d₁ ⟧b idp₀ ]
              =⟨ transp-cBB-r d₁ (pcBA ba⟦ d₁ ⟧b idp₀) (ap g p) ⟩
            q[ pcBA ba⟦ d₁ ⟧b idp₀ bb⟦ d₁ ⟧a idp₀ ba⟦ d₁ ⟧b [ ap g p ] ]
              =⟨ ! $ quot-rel $ pcBBr-switch (pcBA ba⟦ d₁ ⟧b idp₀) [ p ] ⟩
            q[ pcBA ba⟦ d₁ ⟧b idp₀ bb⟦ d₁ ⟧a [ ap f p ] ba⟦ d₂ ⟧b idp₀ ]
              =⟨ ! $ transp-cBA-r d₁ pcBA (ap f p) |in-ctx –> (eqv-on-image d₂) ⟩
            –> (eqv-on-image d₂) (transport (codeBA b₀) (ap f p) q[ pcBA ])
              =⟨ ∘-ap (codeBA b₀) f p |in-ctx (λ p → coe p q[ pcBA ]) |in-ctx –> (eqv-on-image d₂) ⟩
            –> (eqv-on-image d₂) (transport (λ c → codeBA b₀ (f c)) p q[ pcBA ])
              =∎)
          (λ _ → prop-has-all-paths-↓ (SetQuot-is-set _ _))

    module SE = SurjExt
      (λ c → ≃-is-set SetQuot-is-set SetQuot-is-set)
      h h-is-surj
      eqv-on-image
      eqv-is-const

    eqv : ∀ c → codeBA b₀ (f c) ≃ codeBB b₀ (g c)
    eqv = SE.surj-ext

    eqv-β : ∀ d → eqv (h d) == eqv-on-image d
    eqv-β = SE.surj-ext-β

  codeBP : B → Pushout span → Type (lmax (lmax (lmax i j) k) l)
  codeBP b₀ = Pushout-rec (codeBA b₀) (codeBB b₀)
    (ua ∘ CodeBAEquivCodeBB.eqv b₀)
