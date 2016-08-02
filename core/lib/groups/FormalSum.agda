{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Group
open import lib.types.Int
open import lib.types.List
open import lib.types.SetQuotient

module lib.groups.FormalSum {i} where

PreFormalSum : Type i → Type i
PreFormalSum A = List (ℤ × A)

module _ {A : Type i} (dec : has-dec-eq A) where

  coef-pre : PreFormalSum A → (A → ℤ)
  coef-pre l a = ℤsum $ map fst $ filter (λ{(_ , a') → dec a' a}) l
  
  -- Extensional equality
  FormalSum-rel : Rel (PreFormalSum A) i
  FormalSum-rel l₁ l₂ = ∀ a → coef-pre l₁ a == coef-pre l₂ a

  -- The quotient
  FormalSum : Type i
  FormalSum = SetQuotient FormalSum-rel

  -- Properties of [coef-pre]
  coef-pre-++ : ∀ l₁ l₂ a
    → coef-pre (l₁ ++ l₂) a == coef-pre l₁ a ℤ+ coef-pre l₂ a
  coef-pre-++ nil              l₂ a = idp
  coef-pre-++ ((z , a') :: l₁) l₂ a with dec a' a
  ... | inl _ = ap (z ℤ+_) (coef-pre-++ l₁ l₂ a)
              ∙ ! (ℤ+-assoc z (coef-pre l₁ a) (coef-pre l₂ a))
  ... | inr _ = coef-pre-++ l₁ l₂ a

  flip-pre : PreFormalSum A → PreFormalSum A
  flip-pre = map λ{(z , a) → (ℤ~ z , a)}

  coef-pre-flip-pre : ∀ l a
    → coef-pre (flip-pre l) a == ℤ~ (coef-pre l a)
  coef-pre-flip-pre nil a = idp
  coef-pre-flip-pre ((z , a') :: l) a with dec a' a
  ... | inl _ = ap (ℤ~ z ℤ+_) (coef-pre-flip-pre l a)
              ∙ ! (ℤ~-ℤ+ z (coef-pre l a))
  ... | inr _ = coef-pre-flip-pre l a

module _ {A : Type i} {dec : has-dec-eq A} where

  coef : FormalSum dec → (A → ℤ)
  coef = SetQuot-rec (→-is-set ℤ-is-set) (coef-pre dec) λ=

  -- extensionality of formal sums.
  coef-ext : ∀ {fs₁ fs₂} → (∀ a → coef fs₁ a == coef fs₂ a) → fs₁ == fs₂
  coef-ext {fs₁} {fs₂} = ext' fs₁ fs₂ where
    ext' : ∀ fs₁ fs₂ → (∀ a → coef fs₁ a == coef fs₂ a) → fs₁ == fs₂
    ext' = SetQuot-elim
      (λ _ → Π-is-set λ _ → →-is-set $ =-preserves-set SetQuotient-is-set)
      (λ l₁ → SetQuot-elim
        (λ _ → →-is-set $ =-preserves-set SetQuotient-is-set)
        (λ l₂ r → quot-rel r)
        (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → SetQuotient-is-set _ _)))
      (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → Π-is-prop λ _ → SetQuotient-is-set _ _))

  -- TODO Use abstract [FormalSum].

  infixl 80 _⊞_
  _⊞_ : FormalSum dec → FormalSum dec → FormalSum dec
  _⊞_ = SetQuot-rec
    (→-is-set SetQuotient-is-set)
    (λ l₁ → SetQuot-rec SetQuotient-is-set (q[_] ∘ (l₁ ++_))
      (λ {l₂} {l₂'} r → quot-rel λ a
        → coef-pre-++ dec l₁ l₂ a
        ∙ ap (coef-pre dec l₁ a ℤ+_) (r a)
        ∙ ! (coef-pre-++ dec l₁ l₂' a)))
    (λ {l₁} {l₁'} r → λ= $ SetQuot-elim
      (λ _ → =-preserves-set SetQuotient-is-set)
      (λ l₂ → quot-rel λ a
        → coef-pre-++ dec l₁ l₂ a
        ∙ ap (_ℤ+ coef-pre dec l₂ a) (r a)
        ∙ ! (coef-pre-++ dec l₁' l₂ a))
      (λ _ → prop-has-all-paths-↓ (SetQuotient-is-set _ _)))

  coef-⊞ : ∀ fs₁ fs₂ a → coef (fs₁ ⊞ fs₂) a == coef fs₁ a ℤ+ coef fs₂ a
  coef-⊞ = SetQuot-elim
    (λ _ → Π-is-set λ _ → Π-is-set λ _ → =-preserves-set ℤ-is-set)
    (λ l₁ → SetQuot-elim
      (λ _ → Π-is-set λ _ → =-preserves-set ℤ-is-set)
      (λ l₂ → coef-pre-++ dec l₁ l₂)
      (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → ℤ-is-set _ _)))
    (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → Π-is-prop λ _ → ℤ-is-set _ _))

  ⊟ : FormalSum dec → FormalSum dec
  ⊟ = SetQuot-rec SetQuotient-is-set (q[_] ∘ flip-pre dec)
    λ {l₁} {l₂} r → quot-rel λ a
      → coef-pre-flip-pre dec l₁ a ∙ ap ℤ~ (r a) ∙ ! (coef-pre-flip-pre dec l₂ a)

  coef-⊟ : ∀ fs a → coef (⊟ fs) a == ℤ~ (coef fs a)
  coef-⊟ = SetQuot-elim
    (λ _ → Π-is-set λ _ → =-preserves-set ℤ-is-set)
    (λ l a → coef-pre-flip-pre dec l a)
    (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → ℤ-is-set _ _))

  ⊞-unit : FormalSum dec
  ⊞-unit = q[ nil ]

  coef-⊞-unit : ∀ a → coef ⊞-unit a == 0
  coef-⊞-unit a = idp

{-
  -- Favonia: These commented-out proofs are valid, but I want to promote
  -- the usage of [coef-ext].

  ⊞-unit-l : ∀ fs → ⊞-unit ⊞ fs == fs
  ⊞-unit-l = SetQuot-elim
    (λ _ → =-preserves-set SetQuotient-is-set)
    (λ l → idp)
    (λ _ → prop-has-all-paths-↓ (SetQuotient-is-set _ _))

  ⊞-unit-r : ∀ fs → fs ⊞ ⊞-unit == fs
  ⊞-unit-r = SetQuot-elim
    (λ _ → =-preserves-set SetQuotient-is-set)
    (λ l → ap q[_] $ ++-nil-r l)
    (λ _ → prop-has-all-paths-↓ (SetQuotient-is-set _ _))
-}

  ⊞-unit-l : ∀ fs → ⊞-unit ⊞ fs == fs
  ⊞-unit-l fs = coef-ext λ a → coef-⊞ ⊞-unit fs a

  ⊞-unit-r : ∀ fs → fs ⊞ ⊞-unit == fs
  ⊞-unit-r fs = coef-ext λ a → coef-⊞ fs ⊞-unit a ∙ ℤ+-unit-r _

  ⊞-assoc : ∀ fs₁ fs₂ fs₃ → (fs₁ ⊞ fs₂) ⊞ fs₃ == fs₁ ⊞ (fs₂ ⊞ fs₃)
  ⊞-assoc fs₁ fs₂ fs₃ = coef-ext λ a →
    coef ((fs₁ ⊞ fs₂) ⊞ fs₃) a
      =⟨ coef-⊞ (fs₁ ⊞ fs₂) fs₃ a ⟩
    coef (fs₁ ⊞ fs₂) a ℤ+ coef fs₃ a
      =⟨ coef-⊞ fs₁ fs₂ a |in-ctx _ℤ+ coef fs₃ a ⟩
    (coef fs₁ a ℤ+ coef fs₂ a) ℤ+ coef fs₃ a
      =⟨ ℤ+-assoc (coef fs₁ a) (coef fs₂ a) (coef fs₃ a) ⟩
    coef fs₁ a ℤ+ (coef fs₂ a ℤ+ coef fs₃ a)
      =⟨ ! $ coef-⊞ fs₂ fs₃ a |in-ctx coef fs₁ a ℤ+_ ⟩
    coef fs₁ a ℤ+ coef (fs₂ ⊞ fs₃) a
      =⟨ ! $ coef-⊞ fs₁ (fs₂ ⊞ fs₃) a ⟩
    coef (fs₁ ⊞ (fs₂ ⊞ fs₃)) a
      ∎

  ⊟-inv-r : ∀ fs → fs ⊞ (⊟ fs) == ⊞-unit
  ⊟-inv-r fs = coef-ext λ a → coef-⊞ fs (⊟ fs) a
                            ∙ ap (coef fs a ℤ+_) (coef-⊟ fs a)
                            ∙ ℤ~-inv-r (coef fs a)

  ⊟-inv-l : ∀ fs → (⊟ fs) ⊞ fs == ⊞-unit
  ⊟-inv-l fs = coef-ext λ a → coef-⊞ (⊟ fs) fs a
                            ∙ ap (_ℤ+ coef fs a) (coef-⊟ fs a)
                            ∙ ℤ~-inv-l (coef fs a)

  FormalSum-group-structure : GroupStructure (FormalSum dec)
  FormalSum-group-structure = record
    { ident = ⊞-unit
    ; inv = ⊟
    ; comp = _⊞_
    ; unitl = ⊞-unit-l
    ; unitr = ⊞-unit-r
    ; assoc = ⊞-assoc
    ; invr = ⊟-inv-r
    ; invl = ⊟-inv-l
    }

  FormalSum-group : Group i
  FormalSum-group = group _ SetQuotient-is-set FormalSum-group-structure

  has-finite-supports : (A → ℤ) → Type i
  has-finite-supports f = Σ (FormalSum dec) λ fs → ∀ a → f a == coef fs a

  has-finite-supports-is-prop : ∀ f → is-prop (has-finite-supports f)
  has-finite-supports-is-prop f = all-paths-is-prop
    λ{(fs₁ , match₁) (fs₂ , match₂) → pair=
      (coef-ext λ a → ! (match₁ a) ∙ match₂ a)
      (prop-has-all-paths-↓ $ Π-is-prop λ _ → ℤ-is-set _ _)}
