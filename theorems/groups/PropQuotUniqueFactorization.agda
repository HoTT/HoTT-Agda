{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.ConstantToSetExtendsToProp

{-
          q[_]ᴳ
     G/Q ↞------ G
      ↑          ↑
   φ₂ ╎          ╎ inject
      ↑          ↑
      K ↞------- P
           φ₁

     Then, K ≃ᴳ P/Q.
-}

module groups.PropQuotUniqueFactorization {i j₁ j₂ k l₁ l₂}
  {G : Group i} {H₁ : Group j₁} {H₂ : Group j₂} {K : Group k}
  (P : SubgroupProp G l₁)
  (Q : NormalSubgroupProp G l₂)
  (φ₁ : Subgroup P →ᴳ K) (φ₁-is-surj : is-surjᴳ φ₁)
  (φ₂ : K →ᴳ QuotGroup Q) (φ₂-is-inj : is-injᴳ φ₂)
  (φ-comm : ∀ p → GroupHom.f (φ₂ ∘ᴳ φ₁) p == q[ fst p ])
  where

  private
    module G = Group G
    module K = Group K
    module P = Subgroup P
    module φ₁ = GroupHom φ₁
    module φ₂ = GroupHom φ₂

  P/Q-prop : NormalSubgroupProp (Subgroup P) l₂
  P/Q-prop = quot-of-sub P Q

  P/Q : Group (lmax i (lmax l₁ l₂))
  P/Q = QuotGroup P/Q-prop

  private
    module P/Q = Group P/Q
    module _ (k : Group.El K) where
      K-to-P/Q-f' : hfiber φ₁.f k → P/Q.El
      K-to-P/Q-f' (p , _) = q[ p ]

      abstract
        K-to-P/Q-f'-const : (hf₁ hf₂ : hfiber φ₁.f k)
          → K-to-P/Q-f' hf₁ == K-to-P/Q-f' hf₂
        K-to-P/Q-f'-const (h₁ , r₁) (h₂ , r₂) =
          quot-relᴳ {P = P/Q-prop} $ <– (quot-relᴳ-equiv {P = Q}) $
            ! (φ-comm h₁) ∙ ap φ₂.f (r₁ ∙ ! r₂) ∙ φ-comm h₂

      K-to-P/Q-f : Trunc -1 (hfiber φ₁.f k) → P/Q.El
      K-to-P/Q-f = cst-extend P/Q.El-is-set K-to-P/Q-f' K-to-P/Q-f'-const

      K-to-P/Q-f-is-const : ∀ hf₁ hf₂ → K-to-P/Q-f hf₁ == K-to-P/Q-f hf₂
      K-to-P/Q-f-is-const = cst-extend-is-const P/Q.El-is-set K-to-P/Q-f' K-to-P/Q-f'-const

    abstract
      K-to-P/Q-f-comp : (k₁ k₂ : K.El)
        → (hf₁₂ : Trunc -1 (hfiber φ₁.f (K.comp k₁ k₂)))
        → (hf₁ : Trunc -1 (hfiber φ₁.f k₁))
        → (hf₂ : Trunc -1 (hfiber φ₁.f k₂))
        → K-to-P/Q-f (K.comp k₁ k₂) hf₁₂ == P/Q.comp (K-to-P/Q-f k₁ hf₁) (K-to-P/Q-f k₂ hf₂)
      K-to-P/Q-f-comp k₁ k₂ hf₁₂ = Trunc-elim
        (λ hf₁ → Π-is-prop λ hf₂ →
          P/Q.El-is-set _ (P/Q.comp (K-to-P/Q-f k₁ hf₁) (K-to-P/Q-f k₂ hf₂)))
        (λ{(p₁ , r₁) → Trunc-elim
          (λ hf₂ → P/Q.El-is-set _ (P/Q.comp q[ p₁ ] (K-to-P/Q-f k₂ hf₂)))
          (λ{(p₂ , r₂) → K-to-P/Q-f-is-const (K.comp k₁ k₂)
              hf₁₂ [ P.comp p₁ p₂ , φ₁.pres-comp p₁ p₂ ∙ ap2 K.comp r₁ r₂ ]})})

  K-to-P/Q : K →ᴳ P/Q
  K-to-P/Q = record {
    f = λ k → K-to-P/Q-f k (φ₁-is-surj k);
    pres-comp = λ k₁ k₂ → K-to-P/Q-f-comp k₁ k₂
      (φ₁-is-surj (K.comp k₁ k₂)) (φ₁-is-surj k₁) (φ₁-is-surj k₂)}

  K-equiv-P/Q : K ≃ᴳ P/Q
  K-equiv-P/Q = K-to-P/Q , is-eq to from to-from from-to where
    to : K.El → P/Q.El
    to = λ k → K-to-P/Q-f k (φ₁-is-surj k)

    from : P/Q.El → K.El
    from = SetQuot-rec K.El-is-set
      (λ p → φ₁.f p)
      (λ {p₁} {p₂} q'p₁p₂⁻¹ → φ₂-is-inj (φ₁.f p₁) (φ₁.f p₂) $
        φ-comm p₁ ∙ quot-relᴳ {P = Q} q'p₁p₂⁻¹ ∙ ! (φ-comm p₂))

    abstract
      to-from : ∀ p/q → to (from p/q) == p/q
      to-from = SetQuot-elim (λ p/q → raise-level -1 $ P/Q.El-is-set _ p/q)
        (λ p → K-to-P/Q-f-is-const (φ₁.f p) (φ₁-is-surj (φ₁.f p)) [ p , idp ])
        (λ _ → prop-has-all-paths-↓ $ P/Q.El-is-set _ _)

      from-to' : ∀ k (hf : Trunc -1 (hfiber φ₁.f k)) → from (K-to-P/Q-f k hf) == k
      from-to' k = Trunc-elim (λ hf → K.El-is-set (from (K-to-P/Q-f k hf)) k) (λ{(p , r) → r})

      from-to : ∀ k → from (to k) == k
      from-to k = from-to' k (φ₁-is-surj k)
