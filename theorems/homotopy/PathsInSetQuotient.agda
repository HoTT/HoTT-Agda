{-# OPTIONS --without-K #-}

open import HoTT

module homotopy.PathsInSetQuotient {i j} (A : Type i)
  (rel : Rel A j)
  (rel-is-prop : ∀ {a b} → is-prop (rel a b))
  (rel-is-refl : ∀ a → rel a a)
  (rel-is-sym : ∀ {a b} → rel a b → rel b a)
  (rel-is-trans : ∀ {a b c} → rel a b → rel b c → rel a c)
  where

  private
    Q : Type (lmax i j)
    Q = SetQuotient rel

    rel'-over-quot : Q → Q → hProp j
    rel'-over-quot = SetQuot-rec (→-is-set $ hProp-is-set j)
      (λ a → SetQuot-rec (hProp-is-set j)
        (λ b → rel a b , rel-is-prop)
        (λ rb₁b₂ → nType=-out $ ua $ equiv
          (λ rab₁ → rel-is-trans rab₁ rb₁b₂)
          (λ rab₂ → rel-is-trans rab₂ (rel-is-sym rb₁b₂))
          (λ _ → prop-has-all-paths rel-is-prop _ _)
          (λ _ → prop-has-all-paths rel-is-prop _ _)))
      (λ ra₁a₂ → λ= $ SetQuot-elim
        (λ _ → prop-has-level-S $ hProp-is-set j _ _)
        (λ b → nType=-out $ ua $ equiv
          (λ ra₁b → rel-is-trans (rel-is-sym ra₁a₂) ra₁b)
          (λ ra₂b → rel-is-trans ra₁a₂ ra₂b)
          (λ _ → prop-has-all-paths rel-is-prop _ _)
          (λ _ → prop-has-all-paths rel-is-prop _ _))
        (λ _ → prop-has-all-paths-↓ $ hProp-is-set j _ _))

    rel-over-quot : Q → Q → Type j
    rel-over-quot q₁ q₂ = fst (rel'-over-quot q₁ q₂)

    abstract
      rel-over-quot-is-prop : {q₁ q₂ : Q} → is-prop (rel-over-quot q₁ q₂)
      rel-over-quot-is-prop {q₁} {q₂} = snd (rel'-over-quot q₁ q₂)

      rel-over-quot-is-refl : (q : Q) → rel-over-quot q q
      rel-over-quot-is-refl = SetQuot-elim
        (λ q → prop-has-level-S (rel-over-quot-is-prop {q} {q}))
        (λ a → rel-is-refl a)
        (λ _ → prop-has-all-paths-↓ rel-is-prop)

      path-to-rel-over-quot : {q₁ q₂ : Q} → q₁ == q₂ → rel-over-quot q₁ q₂
      path-to-rel-over-quot {q} idp = rel-over-quot-is-refl q

  path-equiv-rel : ∀ {a₁ a₂ : A} → (q[ a₁ ] == q[ a₂ ]) ≃ rel a₁ a₂
  path-equiv-rel {a₁} {a₂} = equiv
    (path-to-rel-over-quot {q[ a₁ ]} {q[ a₂ ]}) quot-rel
    (λ _ → prop-has-all-paths rel-is-prop _ _)
    (λ _ → prop-has-all-paths (SetQuotient-is-set _ _) _ _)
