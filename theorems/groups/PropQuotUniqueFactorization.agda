{-# OPTIONS --without-K --rewriting #-}

open import HoTT
import homotopy.ConstantToSetExtendsToProp as ConstExt

{-
          q[_]ᴳ
     G/Q ↞------ G
      ↑          ↑
   φ₂ ╎          ╎ inject
      ↑          ↑
      H ↞------- P
           φ₁

     Then, H ≃ᴳ P/Q.
-}

module groups.PropQuotUniqueFactorization
  {i j l₁ l₂} {G : Group i} {H : Group j}
  (P : SubgroupProp G l₁)
  (Q : NormalSubgroupProp G l₂)
  (φ₁ : Subgroup P →ᴳ H) (φ₁-is-surj : is-surjᴳ φ₁)
  (φ₂ : H →ᴳ QuotGroup Q) (φ₂-is-inj : is-injᴳ φ₂)
  (φ-comm : ∀ p → GroupHom.f (φ₂ ∘ᴳ φ₁) p == q[ fst p ])
  where

  private
    module G = Group G
    module H = Group H
    module P = Subgroup P
    module φ₁ = GroupHom φ₁
    module φ₂ = GroupHom φ₂

    P/Q-prop : NormalSubgroupProp (Subgroup P) l₂
    P/Q-prop = quot-of-sub P Q

    P/Q : Group (lmax i (lmax l₁ l₂))
    P/Q = QuotGroup P/Q-prop

    module P/Q = Group P/Q
    module _ (k : Group.El H) where
      H-to-P/Q-f' : hfiber φ₁.f k → P/Q.El
      H-to-P/Q-f' (p , _) = q[ p ]

      abstract
        H-to-P/Q-f'-const : (hf₁ hf₂ : hfiber φ₁.f k)
          → H-to-P/Q-f' hf₁ == H-to-P/Q-f' hf₂
        H-to-P/Q-f'-const (h₁ , r₁) (h₂ , r₂) =
          quot-relᴳ {P = P/Q-prop} $ <– (quot-relᴳ-equiv {P = Q}) $
            ! (φ-comm h₁) ∙ ap φ₂.f (r₁ ∙ ! r₂) ∙ φ-comm h₂

      module HToP/Q = ConstExt P/Q.El-is-set
        H-to-P/Q-f' H-to-P/Q-f'-const

      H-to-P/Q-f : Trunc -1 (hfiber φ₁.f k) → P/Q.El
      H-to-P/Q-f = HToP/Q.ext

      H-to-P/Q-f-is-const : ∀ hf₁ hf₂ → H-to-P/Q-f hf₁ == H-to-P/Q-f hf₂
      H-to-P/Q-f-is-const = HToP/Q.ext-is-const

    abstract
      H-to-P/Q-f-comp : (k₁ k₂ : H.El)
        → (hf₁₂ : Trunc -1 (hfiber φ₁.f (H.comp k₁ k₂)))
        → (hf₁ : Trunc -1 (hfiber φ₁.f k₁))
        → (hf₂ : Trunc -1 (hfiber φ₁.f k₂))
        → H-to-P/Q-f (H.comp k₁ k₂) hf₁₂ == P/Q.comp (H-to-P/Q-f k₁ hf₁) (H-to-P/Q-f k₂ hf₂)
      H-to-P/Q-f-comp k₁ k₂ hf₁₂ = Trunc-elim
        (λ hf₁ → Π-is-prop λ hf₂ →
          P/Q.El-is-set _ (P/Q.comp (H-to-P/Q-f k₁ hf₁) (H-to-P/Q-f k₂ hf₂)))
        (λ{(p₁ , r₁) → Trunc-elim
          (λ hf₂ → P/Q.El-is-set _ (P/Q.comp q[ p₁ ] (H-to-P/Q-f k₂ hf₂)))
          (λ{(p₂ , r₂) → H-to-P/Q-f-is-const (H.comp k₁ k₂)
              hf₁₂ [ P.comp p₁ p₂ , φ₁.pres-comp p₁ p₂ ∙ ap2 H.comp r₁ r₂ ]})})

  H-to-P/Q : H →ᴳ P/Q
  H-to-P/Q = record {
    f = λ k → H-to-P/Q-f k (φ₁-is-surj k);
    pres-comp = λ k₁ k₂ → H-to-P/Q-f-comp k₁ k₂
      (φ₁-is-surj (H.comp k₁ k₂)) (φ₁-is-surj k₁) (φ₁-is-surj k₂)}

  H-iso-P/Q : H ≃ᴳ P/Q
  H-iso-P/Q = H-to-P/Q , is-eq to from to-from from-to where
    to : H.El → P/Q.El
    to = λ k → H-to-P/Q-f k (φ₁-is-surj k)

    from : P/Q.El → H.El
    from = SetQuot-rec H.El-is-set
      (λ p → φ₁.f p)
      (λ {p₁} {p₂} q'p₁p₂⁻¹ → φ₂-is-inj (φ₁.f p₁) (φ₁.f p₂) $
        φ-comm p₁ ∙ quot-relᴳ {P = Q} q'p₁p₂⁻¹ ∙ ! (φ-comm p₂))

    abstract
      to-from : ∀ p/q → to (from p/q) == p/q
      to-from = SetQuot-elim (λ p/q → raise-level -1 $ P/Q.El-is-set _ p/q)
        (λ p → H-to-P/Q-f-is-const (φ₁.f p) (φ₁-is-surj (φ₁.f p)) [ p , idp ])
        (λ _ → prop-has-all-paths-↓ $ P/Q.El-is-set _ _)

      from-to' : ∀ k (hf : Trunc -1 (hfiber φ₁.f k)) → from (H-to-P/Q-f k hf) == k
      from-to' k = Trunc-elim (λ hf → H.El-is-set (from (H-to-P/Q-f k hf)) k) (λ{(p , r) → r})

      from-to : ∀ k → from (to k) == k
      from-to k = from-to' k (φ₁-is-surj k)
