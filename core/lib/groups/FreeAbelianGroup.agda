{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Empty
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Group
open import lib.types.Nat
open import lib.types.Int
open import lib.types.List
open import lib.types.SetQuotient
open import lib.groups.Homomorphisms

-- TODO Define [FormalSum] as an abstract type.

module lib.groups.FreeAbelianGroup {i} where

PlusMinus : Type i → Type i
PlusMinus A = Coprod A A

PreFormalSum : Type i → Type i
PreFormalSum A = List (PlusMinus A)

module _ {A : Type i} where

  flip : PlusMinus A → PlusMinus A
  flip (inl a) = inr a
  flip (inr a) = inl a

  flip-flip : ∀ x → flip (flip x) == x
  flip-flip (inl x) = idp
  flip-flip (inr x) = idp

  flip-all : PreFormalSum A → PreFormalSum A
  flip-all = map flip

  -- Extensional equality
  data FormalSumRel : PreFormalSum A → PreFormalSum A → Type i where
    fsr-refl : ∀ {l₁ l₂} → l₁ == l₂ → FormalSumRel l₁ l₂
    fsr-trans : ∀ {l₁ l₂ l₃} → FormalSumRel l₁ l₂ → FormalSumRel l₂ l₃ → FormalSumRel l₁ l₃
    fsr-cons : ∀ x {l₁ l₂} → FormalSumRel l₁ l₂ → FormalSumRel (x :: l₁) (x :: l₂)
    fsr-swap : ∀ x₁ x₂ l → FormalSumRel (x₁ :: x₂ :: l) (x₂ :: x₁ :: l)
    fsr-flip : ∀ x₁ l → FormalSumRel (flip x₁ :: x₁ :: l) l

-- The quotient
FormalSum : Type i → Type i
FormalSum A = SetQuotient (FormalSumRel {A})

□[_] : {A : Type i} → PreFormalSum A → FormalSum A
□[_] = q[_]

FormalSum-level : {A : Type i} → is-set (FormalSum A)
FormalSum-level = SetQuotient-level

FormalSum-is-set = FormalSum-level

module _ {A : Type i} where

  module FormalSumElim {k} {P : FormalSum A → Type k}
    (p : (x : FormalSum A) → is-set (P x)) (incl* : (a : PreFormalSum A) → P □[ a ])
    (rel* : ∀ {a₁ a₂} (r : FormalSumRel a₁ a₂) → incl* a₁ == incl* a₂ [ P ↓ quot-rel r ])
    = SetQuotElim p incl* rel*
  open FormalSumElim public renaming (f to FormalSum-elim) hiding (quot-rel-β)

  module FormalSumRec {k} {B : Type k} (p : is-set B) (incl* : PreFormalSum A → B)
    (rel* : ∀ {a₁ a₂} (r : FormalSumRel a₁ a₂) → incl* a₁ == incl* a₂)
    = SetQuotRec p incl* rel*
  open FormalSumRec public renaming (f to FormalSum-rec)

  abstract
    FormalSumRel-cong-++-l :
      ∀ {l₁ l₁'} → FormalSumRel {A} l₁ l₁'
      → (l₂ : PreFormalSum A)
      → FormalSumRel (l₁ ++ l₂) (l₁' ++ l₂)
    FormalSumRel-cong-++-l (fsr-refl idp) l₂ = fsr-refl idp
    FormalSumRel-cong-++-l (fsr-trans fsr₁ fsr₂) l₂ = fsr-trans (FormalSumRel-cong-++-l fsr₁ l₂) (FormalSumRel-cong-++-l fsr₂ l₂)
    FormalSumRel-cong-++-l (fsr-cons x fsr₁) l₂ = fsr-cons x (FormalSumRel-cong-++-l fsr₁ l₂)
    FormalSumRel-cong-++-l (fsr-swap x₁ x₂ l₁) l₂ = fsr-swap x₁ x₂ (l₁ ++ l₂)
    FormalSumRel-cong-++-l (fsr-flip x₁ l₁) l₂ = fsr-flip x₁ (l₁ ++ l₂)

    FormalSumRel-cong-++-r :
      ∀ (l₁ : PreFormalSum A)
      → ∀ {l₂ l₂'} → FormalSumRel l₂ l₂'
      → FormalSumRel (l₁ ++ l₂) (l₁ ++ l₂')
    FormalSumRel-cong-++-r nil fsr₂ = fsr₂
    FormalSumRel-cong-++-r (x :: l₁) fsr₂ = fsr-cons x (FormalSumRel-cong-++-r l₁ fsr₂)

  infixl 80 _⊞_
  _⊞_ : FormalSum A → FormalSum A → FormalSum A
  _⊞_ = FormalSum-rec
    (→-is-set FormalSum-is-set)
    (λ l₁ → FormalSum-rec FormalSum-is-set (λ l₂ → q[ l₁ ++ l₂ ])
      (λ r → quot-rel $ FormalSumRel-cong-++-r l₁ r))
    (λ {l₁} {l₁'} r → λ= $ FormalSum-elim
      (λ _ → =-preserves-set FormalSum-is-set)
      (λ l₂ → quot-rel $ FormalSumRel-cong-++-l r l₂)
      (λ _ → prop-has-all-paths-↓ (FormalSum-is-set _ _)))

  abstract
    FormalSumRel-cong-flip-all : ∀ {l₁ l₂}
      → FormalSumRel {A} l₁ l₂ → FormalSumRel (flip-all l₁) (flip-all l₂)
    FormalSumRel-cong-flip-all (fsr-refl idp) = fsr-refl idp
    FormalSumRel-cong-flip-all (fsr-trans fsr₁ fsr₂) = fsr-trans (FormalSumRel-cong-flip-all fsr₁) (FormalSumRel-cong-flip-all fsr₂)
    FormalSumRel-cong-flip-all (fsr-cons x fsr₁) = fsr-cons (flip x) (FormalSumRel-cong-flip-all fsr₁)
    FormalSumRel-cong-flip-all (fsr-swap x₁ x₂ l) = fsr-swap (flip x₁) (flip x₂) (flip-all l)
    FormalSumRel-cong-flip-all (fsr-flip (inl x) l) = fsr-flip (inr x) (flip-all l)
    FormalSumRel-cong-flip-all (fsr-flip (inr x) l) = fsr-flip (inl x) (flip-all l)

  ⊟ : FormalSum A → FormalSum A
  ⊟ = FormalSum-rec FormalSum-is-set (q[_] ∘ flip-all)
    (λ r → quot-rel $ FormalSumRel-cong-flip-all r)

  ⊞-unit : FormalSum A
  ⊞-unit = q[ nil ]

  ⊞-unit-l : ∀ g → ⊞-unit ⊞ g == g
  ⊞-unit-l = FormalSum-elim
    (λ _ → =-preserves-set FormalSum-is-set)
    (λ _ → idp)
    (λ _ → prop-has-all-paths-↓ (FormalSum-is-set _ _))

  ⊞-unit-r : ∀ g → g ⊞ ⊞-unit == g
  ⊞-unit-r = FormalSum-elim
    (λ _ → =-preserves-set FormalSum-is-set)
    (λ _ → ap q[_] $ ++-unit-r _)
    (λ _ → prop-has-all-paths-↓ (FormalSum-is-set _ _))

  ⊞-assoc : ∀ g₁ g₂ g₃ → (g₁ ⊞ g₂) ⊞ g₃ == g₁ ⊞ (g₂ ⊞ g₃)
  ⊞-assoc = FormalSum-elim (λ _ → Π-is-set λ _ → Π-is-set λ _ → =-preserves-set FormalSum-is-set)
    (λ l₁ → FormalSum-elim (λ _ → Π-is-set λ _ → =-preserves-set FormalSum-is-set)
      (λ l₂ → FormalSum-elim (λ _ → =-preserves-set FormalSum-is-set)
        (λ l₃ → ap q[_] $ ++-assoc l₁ l₂ l₃)
        (λ _ → prop-has-all-paths-↓ $ FormalSum-is-set _ _))
      (λ _ → prop-has-all-paths-↓ $ Π-is-prop λ _ → FormalSum-is-set _ _))
    (λ _ → prop-has-all-paths-↓ $ Π-is-prop λ _ → Π-is-prop λ _ → FormalSum-is-set _ _)

  abstract
    FormalSumRel-swap1 : ∀ x l₁ l₂ → FormalSumRel {A} (l₁ ++ l[ x ] ++ l₂) (x :: l₁ ++ l₂)
    FormalSumRel-swap1 x nil l₂ = fsr-refl idp
    FormalSumRel-swap1 x (x₁ :: l₁) l₂ = fsr-trans (fsr-cons x₁ (FormalSumRel-swap1 x l₁ l₂)) (fsr-swap x₁ x (l₁ ++ l₂))

    PreFormalSum-inv-r : ∀ l → FormalSumRel {A} (l ++ flip-all l) nil
    PreFormalSum-inv-r nil = fsr-refl idp
    PreFormalSum-inv-r (x :: l) =
      fsr-trans (FormalSumRel-swap1 (flip x) (x :: l) (flip-all l)) $
      fsr-trans (fsr-flip x (l ++ flip-all l)) (PreFormalSum-inv-r l)

  ⊟-inv-r : ∀ g → g ⊞ (⊟ g) == ⊞-unit
  ⊟-inv-r = FormalSum-elim
    (λ _ → =-preserves-set FormalSum-is-set)
    (λ l → quot-rel (PreFormalSum-inv-r l))
    (λ _ → prop-has-all-paths-↓ (FormalSum-is-set _ _))

  abstract
    PreFormalSum-inv-l : ∀ l → FormalSumRel {A} (flip-all l ++ l) nil
    PreFormalSum-inv-l nil = fsr-refl idp
    PreFormalSum-inv-l (x :: l) =
      fsr-trans (FormalSumRel-swap1 x (flip x :: flip-all l) l) $
      fsr-trans (fsr-refl (ap (_:: flip x :: flip-all l ++ l) (! (flip-flip x)))) $
      fsr-trans (fsr-flip (flip x) (flip-all l ++ l)) (PreFormalSum-inv-l l)

  ⊟-inv-l : ∀ g → (⊟ g) ⊞ g == ⊞-unit
  ⊟-inv-l = FormalSum-elim
    (λ _ → =-preserves-set FormalSum-is-set)
    (λ l → quot-rel (PreFormalSum-inv-l l))
    (λ _ → prop-has-all-paths-↓ (FormalSum-is-set _ _))

  abstract
    FormalSumRel-swap : ∀ l₁ l₂ → FormalSumRel {A} (l₁ ++ l₂) (l₂ ++ l₁)
    FormalSumRel-swap l₁ nil = fsr-refl (++-unit-r l₁)
    FormalSumRel-swap l₁ (x :: l₂) = fsr-trans (FormalSumRel-swap1 x l₁ l₂) (fsr-cons x (FormalSumRel-swap l₁ l₂))

  ⊞-comm : ∀ g₁ g₂ → g₁ ⊞ g₂ == g₂ ⊞ g₁
  ⊞-comm = FormalSum-elim
    (λ _ → Π-is-set λ _ → =-preserves-set FormalSum-is-set)
    (λ l₁ → FormalSum-elim (λ _ → =-preserves-set FormalSum-is-set)
      (λ l₂ → quot-rel $ FormalSumRel-swap l₁ l₂)
      (λ _ → prop-has-all-paths-↓ (FormalSum-is-set _ _)))
    (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → FormalSum-is-set _ _))

FormalSum-group-structure : (A : Type i) → GroupStructure (FormalSum A)
FormalSum-group-structure A = record
  { ident = ⊞-unit
  ; inv = ⊟
  ; comp = _⊞_
  ; unit-l = ⊞-unit-l
  ; unit-r = ⊞-unit-r
  ; assoc = ⊞-assoc
  ; inv-r = ⊟-inv-r
  ; inv-l = ⊟-inv-l
  }

FreeAbelianGroup : Type i → Group i
FreeAbelianGroup A = group _ FormalSum-is-set (FormalSum-group-structure A)

FreeAbelianGroup-is-abelian : (A : Type i) → is-abelian (FreeAbelianGroup A)
FreeAbelianGroup-is-abelian A = ⊞-comm

module _ {A : Type i} {j} (G : AbelianGroup j) where

  private
    module G = AbelianGroup G

    PlusMinus-lift : (A → G.El) → (PlusMinus A → G.El)
    PlusMinus-lift f (inl a) = f a
    PlusMinus-lift f (inr a) = G.inv (f a)

    PreFormalSum-lift : (A → G.El) → (PreFormalSum A → G.El)
    PreFormalSum-lift f = foldr G.comp G.ident ∘ map (PlusMinus-lift f)

    abstract
      PreFormalSum-lift-emap : ∀ f {l₁ l₂}
        → FormalSumRel {A} l₁ l₂
        → PreFormalSum-lift f l₁ == PreFormalSum-lift f l₂
      PreFormalSum-lift-emap f (fsr-refl idp) = idp
      PreFormalSum-lift-emap f (fsr-trans fsr fsr₁) = (PreFormalSum-lift-emap f fsr) ∙ (PreFormalSum-lift-emap f fsr₁)
      PreFormalSum-lift-emap f (fsr-cons x fsr) = ap (G.comp (PlusMinus-lift f x)) (PreFormalSum-lift-emap f fsr)
      PreFormalSum-lift-emap f (fsr-swap x₁ x₂ l) =
          ! (G.assoc (PlusMinus-lift f x₁) (PlusMinus-lift f x₂) (PreFormalSum-lift f l))
        ∙ ap (λ g → G.comp g (PreFormalSum-lift f l)) (G.comm (PlusMinus-lift f x₁) (PlusMinus-lift f x₂))
        ∙ G.assoc (PlusMinus-lift f x₂) (PlusMinus-lift f x₁) (PreFormalSum-lift f l)
      PreFormalSum-lift-emap f (fsr-flip (inl x) l) =
          ! (G.assoc (G.inv (f x)) (f x) (PreFormalSum-lift f l))
        ∙ ap (λ g → G.comp g (PreFormalSum-lift f l)) (G.inv-l (f x)) ∙ G.unit-l _
      PreFormalSum-lift-emap f (fsr-flip (inr x) l) =
          ! (G.assoc (f x) (G.inv (f x)) (PreFormalSum-lift f l))
        ∙ ap (λ g → G.comp g (PreFormalSum-lift f l)) (G.inv-r (f x)) ∙ G.unit-l _

      PreFormalSum-lift-++ : ∀ f l₁ l₂
        → PreFormalSum-lift f (l₁ ++ l₂) == G.comp (PreFormalSum-lift f l₁) (PreFormalSum-lift f l₂)
      PreFormalSum-lift-++ f nil l₂ = ! $ G.unit-l _
      PreFormalSum-lift-++ f (x :: l₁) l₂ =
          ap (G.comp (PlusMinus-lift f x)) (PreFormalSum-lift-++ f l₁ l₂)
        ∙ ! (G.assoc (PlusMinus-lift f x) (PreFormalSum-lift f l₁)  (PreFormalSum-lift f l₂))

  FreeAbelianGroup-lift : (A → G.El) → (FreeAbelianGroup A →ᴳ G.grp)
  FreeAbelianGroup-lift f = record {
    f = FormalSum-rec G.El-level (PreFormalSum-lift f)
          (λ r → PreFormalSum-lift-emap f r);
    pres-comp =
      FormalSum-elim (λ _ → Π-is-set λ _ → =-preserves-set G.El-level)
        (λ l₁ → FormalSum-elim
          (λ _ → =-preserves-set G.El-level)
          (λ l₂ → PreFormalSum-lift-++ f l₁ l₂)
          (λ _ → prop-has-all-paths-↓ (G.El-level _ _)))
        (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → G.El-level _ _))}

  private
    module _ (hom : FreeAbelianGroup A →ᴳ G.grp) where
      open GroupHom hom
      f* : A → G.El
      f* a = f q[ inl a :: nil ]

      abstract
        PlusMinus-lift-hom : ∀ x → PlusMinus-lift f* x == f q[ x :: nil ]
        PlusMinus-lift-hom (inl x) = idp
        PlusMinus-lift-hom (inr x) = ! $ pres-inv q[ inl x :: nil ]

        PreFormalSum-lift-hom : ∀ l → PreFormalSum-lift f* l == f q[ l ]
        PreFormalSum-lift-hom nil = ! pres-ident
        PreFormalSum-lift-hom (x :: l) = ap2 G.comp (PlusMinus-lift-hom x) (PreFormalSum-lift-hom l) ∙ ! (pres-comp _ _)

    FreeAbelianGroup-lift-is-equiv : is-equiv FreeAbelianGroup-lift
    FreeAbelianGroup-lift-is-equiv = is-eq _ from to-from from-to where
      to = FreeAbelianGroup-lift
      from = f*

      to-from : ∀ h → to (from h) == h
      to-from h = group-hom= $ λ= $ FormalSum-elim
        (λ _ → =-preserves-set G.El-level)
        (λ l → PreFormalSum-lift-hom h l)
        (λ _ → prop-has-all-paths-↓ (G.El-level _ _))

      from-to : ∀ f → from (to f) == f
      from-to f = λ= λ a → G.unit-r (f a)

{-
  TODO Recreate [has-finite-supports]

  has-finite-supports : (A → ℤ) → Type i
  has-finite-supports f = Σ (FormalSum dec) λ g → ∀ a → f a == coef g a

  has-finite-supports-is-prop : ∀ f → is-prop (has-finite-supports f)
  has-finite-supports-is-prop f = all-paths-is-prop
    λ{(g₁ , match₁) (g₂ , match₂) → pair=
      (coef-ext λ a → ! (match₁ a) ∙ match₂ a)
      (prop-has-all-paths-↓ $ Π-is-prop λ _ → ℤ-is-set _ _)}
-}
