{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Empty
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Group
open import lib.types.Nat
open import lib.types.List
open import lib.types.Word
open import lib.types.SetQuotient
open import lib.groups.Homomorphism

module lib.groups.FreeAbelianGroup {i} where

data FormalSumRel {A : Type i} : Word A → Word A → Type i where
  fsr-refl : ∀ {l₁ l₂} → l₁ == l₂ → FormalSumRel l₁ l₂
  fsr-trans : ∀ {l₁ l₂ l₃} → FormalSumRel l₁ l₂ → FormalSumRel l₂ l₃ → FormalSumRel l₁ l₃
  fsr-cons : ∀ x {l₁ l₂} → FormalSumRel l₁ l₂ → FormalSumRel (x :: l₁) (x :: l₂)
  fsr-swap : ∀ x₁ x₂ l → FormalSumRel (x₁ :: x₂ :: l) (x₂ :: x₁ :: l)
  fsr-flip : ∀ x₁ l → FormalSumRel (x₁ :: flip x₁ :: l) l

-- The quotient
FormalSum : Type i → Type i
FormalSum A = SetQuotient (FormalSumRel {A})

module _ {A : Type i} where

  fs[_] : Word A → FormalSum A
  fs[_] = q[_]

  FormalSum-level : is-set (FormalSum A)
  FormalSum-level = SetQuotient-level

  FormalSum-is-set = FormalSum-level

  module FormalSumElim {k} {P : FormalSum A → Type k}
    (p : (x : FormalSum A) → is-set (P x)) (incl* : (a : Word A) → P fs[ a ])
    (rel* : ∀ {a₁ a₂} (r : FormalSumRel a₁ a₂) → incl* a₁ == incl* a₂ [ P ↓ quot-rel r ])
    = SetQuotElim p incl* rel*
  open FormalSumElim public renaming (f to FormalSum-elim) hiding (quot-rel-β)

  module FormalSumRec {k} {B : Type k} (p : is-set B) (incl* : Word A → B)
    (rel* : ∀ {a₁ a₂} (r : FormalSumRel a₁ a₂) → incl* a₁ == incl* a₂)
    = SetQuotRec p incl* rel*
  open FormalSumRec public renaming (f to FormalSum-rec)

module _ (A : Type i) where
  private
    abstract
      FormalSumRel-cong-++-l :
        ∀ {l₁ l₁'} → FormalSumRel {A} l₁ l₁'
        → (l₂ : Word A)
        → FormalSumRel (l₁ ++ l₂) (l₁' ++ l₂)
      FormalSumRel-cong-++-l (fsr-refl idp) l₂ = fsr-refl idp
      FormalSumRel-cong-++-l (fsr-trans fsr₁ fsr₂) l₂ = fsr-trans (FormalSumRel-cong-++-l fsr₁ l₂) (FormalSumRel-cong-++-l fsr₂ l₂)
      FormalSumRel-cong-++-l (fsr-cons x fsr₁) l₂ = fsr-cons x (FormalSumRel-cong-++-l fsr₁ l₂)
      FormalSumRel-cong-++-l (fsr-swap x₁ x₂ l₁) l₂ = fsr-swap x₁ x₂ (l₁ ++ l₂)
      FormalSumRel-cong-++-l (fsr-flip x₁ l₁) l₂ = fsr-flip x₁ (l₁ ++ l₂)

      FormalSumRel-cong-++-r :
        ∀ (l₁ : Word A)
        → ∀ {l₂ l₂'} → FormalSumRel l₂ l₂'
        → FormalSumRel (l₁ ++ l₂) (l₁ ++ l₂')
      FormalSumRel-cong-++-r nil fsr₂ = fsr₂
      FormalSumRel-cong-++-r (x :: l₁) fsr₂ = fsr-cons x (FormalSumRel-cong-++-r l₁ fsr₂)

    infixl 80 _⊞_
    _⊞_ : FormalSum A → FormalSum A → FormalSum A
    _⊞_ = FormalSum-rec
      (→-is-set FormalSum-is-set)
      (λ l₁ → FormalSum-rec FormalSum-is-set (λ l₂ → fs[ l₁ ++ l₂ ])
        (λ r → quot-rel $ FormalSumRel-cong-++-r l₁ r))
      (λ {l₁} {l₁'} r → λ= $ FormalSum-elim
        (λ _ → =-preserves-set FormalSum-is-set)
        (λ l₂ → quot-rel $ FormalSumRel-cong-++-l r l₂)
        (λ _ → prop-has-all-paths-↓ (FormalSum-is-set _ _)))

    abstract
      FormalSumRel-cong-flip : ∀ {l₁ l₂}
        → FormalSumRel {A} l₁ l₂ → FormalSumRel (Word-flip l₁) (Word-flip l₂)
      FormalSumRel-cong-flip (fsr-refl idp) = fsr-refl idp
      FormalSumRel-cong-flip (fsr-trans fsr₁ fsr₂) = fsr-trans (FormalSumRel-cong-flip fsr₁) (FormalSumRel-cong-flip fsr₂)
      FormalSumRel-cong-flip (fsr-cons x fsr₁) = fsr-cons (flip x) (FormalSumRel-cong-flip fsr₁)
      FormalSumRel-cong-flip (fsr-swap x₁ x₂ l) = fsr-swap (flip x₁) (flip x₂) (Word-flip l)
      FormalSumRel-cong-flip (fsr-flip (inl x) l) = fsr-flip (inr x) (Word-flip l)
      FormalSumRel-cong-flip (fsr-flip (inr x) l) = fsr-flip (inl x) (Word-flip l)

    ⊟ : FormalSum A → FormalSum A
    ⊟ = FormalSum-rec FormalSum-is-set (fs[_] ∘ Word-flip)
      (λ r → quot-rel $ FormalSumRel-cong-flip r)

    ⊞-unit : FormalSum A
    ⊞-unit = fs[ nil ]

    ⊞-unit-l : ∀ g → ⊞-unit ⊞ g == g
    ⊞-unit-l = FormalSum-elim
      (λ _ → =-preserves-set FormalSum-is-set)
      (λ _ → idp)
      (λ _ → prop-has-all-paths-↓ (FormalSum-is-set _ _))

    ⊞-unit-r : ∀ g → g ⊞ ⊞-unit == g
    ⊞-unit-r = FormalSum-elim
      (λ _ → =-preserves-set FormalSum-is-set)
      (λ _ → ap fs[_] $ ++-unit-r _)
      (λ _ → prop-has-all-paths-↓ (FormalSum-is-set _ _))

    ⊞-assoc : ∀ g₁ g₂ g₃ → (g₁ ⊞ g₂) ⊞ g₃ == g₁ ⊞ (g₂ ⊞ g₃)
    ⊞-assoc = FormalSum-elim (λ _ → Π-is-set λ _ → Π-is-set λ _ → =-preserves-set FormalSum-is-set)
      (λ l₁ → FormalSum-elim (λ _ → Π-is-set λ _ → =-preserves-set FormalSum-is-set)
        (λ l₂ → FormalSum-elim (λ _ → =-preserves-set FormalSum-is-set)
          (λ l₃ → ap fs[_] $ ++-assoc l₁ l₂ l₃)
          (λ _ → prop-has-all-paths-↓ $ FormalSum-is-set _ _))
        (λ _ → prop-has-all-paths-↓ $ Π-is-prop λ _ → FormalSum-is-set _ _))
      (λ _ → prop-has-all-paths-↓ $ Π-is-prop λ _ → Π-is-prop λ _ → FormalSum-is-set _ _)

    abstract
      FormalSumRel-swap1 : ∀ x l₁ l₂ → FormalSumRel {A} (l₁ ++ (x :: l₂)) (x :: l₁ ++ l₂)
      FormalSumRel-swap1 x nil l₂ = fsr-refl idp
      FormalSumRel-swap1 x (x₁ :: l₁) l₂ = fsr-trans (fsr-cons x₁ (FormalSumRel-swap1 x l₁ l₂)) (fsr-swap x₁ x (l₁ ++ l₂))

      Word-inv-r : ∀ l → FormalSumRel {A} (l ++ Word-flip l) nil
      Word-inv-r nil = fsr-refl idp
      Word-inv-r (x :: l) =
        fsr-trans (FormalSumRel-swap1 (flip x) (x :: l) (Word-flip l)) $
        fsr-trans (fsr-swap (flip x) x (l ++ Word-flip l)) $
        fsr-trans (fsr-flip x (l ++ Word-flip l)) (Word-inv-r l)

    ⊟-inv-r : ∀ g → g ⊞ (⊟ g) == ⊞-unit
    ⊟-inv-r = FormalSum-elim
      (λ _ → =-preserves-set FormalSum-is-set)
      (λ l → quot-rel (Word-inv-r l))
      (λ _ → prop-has-all-paths-↓ (FormalSum-is-set _ _))

    abstract
      Word-inv-l : ∀ l → FormalSumRel {A} (Word-flip l ++ l) nil
      Word-inv-l nil = fsr-refl idp
      Word-inv-l (x :: l) =
        fsr-trans (FormalSumRel-swap1 x (flip x :: Word-flip l) l) $
        fsr-trans (fsr-flip x (Word-flip l ++ l)) (Word-inv-l l)

    ⊟-inv-l : ∀ g → (⊟ g) ⊞ g == ⊞-unit
    ⊟-inv-l = FormalSum-elim
      (λ _ → =-preserves-set FormalSum-is-set)
      (λ l → quot-rel (Word-inv-l l))
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

  FormalSum-group-structure : GroupStructure (FormalSum A)
  FormalSum-group-structure = record
    { ident = ⊞-unit
    ; inv = ⊟
    ; comp = _⊞_
    ; unit-l = ⊞-unit-l
    ; unit-r = ⊞-unit-r
    ; assoc = ⊞-assoc
    ; inv-r = ⊟-inv-r
    ; inv-l = ⊟-inv-l
    }

  FreeAbelianGroup : Group i
  FreeAbelianGroup = group _ FormalSum-is-set FormalSum-group-structure

  FreeAbelianGroup-is-abelian : is-abelian FreeAbelianGroup
  FreeAbelianGroup-is-abelian = ⊞-comm

-- freeness
module _ {A : Type i} {j} (G : AbelianGroup j) where

  private
    module G = AbelianGroup G

    abstract
      Word-extendᴳ-emap : ∀ f {l₁ l₂}
        → FormalSumRel {A} l₁ l₂
        → Word-extendᴳ G.grp f l₁ == Word-extendᴳ G.grp f l₂
      Word-extendᴳ-emap f (fsr-refl idp) = idp
      Word-extendᴳ-emap f (fsr-trans fsr fsr₁) = (Word-extendᴳ-emap f fsr) ∙ (Word-extendᴳ-emap f fsr₁)
      Word-extendᴳ-emap f (fsr-cons x fsr) = ap (G.comp (PlusMinus-extendᴳ G.grp f x)) (Word-extendᴳ-emap f fsr)
      Word-extendᴳ-emap f (fsr-swap x₁ x₂ l) =
          ! (G.assoc (PlusMinus-extendᴳ G.grp f x₁) (PlusMinus-extendᴳ G.grp f x₂) (Word-extendᴳ G.grp f l))
        ∙ ap (λ g → G.comp g (Word-extendᴳ G.grp f l)) (G.comm (PlusMinus-extendᴳ G.grp f x₁) (PlusMinus-extendᴳ G.grp f x₂))
        ∙ G.assoc (PlusMinus-extendᴳ G.grp f x₂) (PlusMinus-extendᴳ G.grp f x₁) (Word-extendᴳ G.grp f l)
      Word-extendᴳ-emap f (fsr-flip (inl x) l) =
          ! (G.assoc (f x) (G.inv (f x)) (Word-extendᴳ G.grp f l))
        ∙ ap (λ g → G.comp g (Word-extendᴳ G.grp f l)) (G.inv-r (f x)) ∙ G.unit-l _
      Word-extendᴳ-emap f (fsr-flip (inr x) l) =
          ! (G.assoc (G.inv (f x)) (f x) (Word-extendᴳ G.grp f l))
        ∙ ap (λ g → G.comp g (Word-extendᴳ G.grp f l)) (G.inv-l (f x)) ∙ G.unit-l _

  FreeAbelianGroup-extend : (A → G.El) → (FreeAbelianGroup A →ᴳ G.grp)
  FreeAbelianGroup-extend f = record {
    f = FormalSum-rec G.El-level (Word-extendᴳ G.grp f)
          (λ r → Word-extendᴳ-emap f r);
    pres-comp =
      FormalSum-elim (λ _ → Π-is-set λ _ → =-preserves-set G.El-level)
        (λ l₁ → FormalSum-elim
          (λ _ → =-preserves-set G.El-level)
          (λ l₂ → Word-extendᴳ-++ G.grp f l₁ l₂)
          (λ _ → prop-has-all-paths-↓ (G.El-level _ _)))
        (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → G.El-level _ _))}

  private
    module Lemma (hom : FreeAbelianGroup A →ᴳ G.grp) where
      open GroupHom hom
      f* : A → G.El
      f* a = f fs[ inl a :: nil ]

      abstract
        PlusMinus-extend-hom : ∀ x → PlusMinus-extendᴳ G.grp f* x == f fs[ x :: nil ]
        PlusMinus-extend-hom (inl x) = idp
        PlusMinus-extend-hom (inr x) = ! $ pres-inv fs[ inl x :: nil ]

        Word-extend-hom : ∀ l → Word-extendᴳ G.grp f* l == f fs[ l ]
        Word-extend-hom nil = ! pres-ident
        Word-extend-hom (x :: l) = ap2 G.comp (PlusMinus-extend-hom x) (Word-extend-hom l) ∙ ! (pres-comp _ _)
    open Lemma

  FreeAbelianGroup-extend-is-equiv : is-equiv FreeAbelianGroup-extend
  FreeAbelianGroup-extend-is-equiv = is-eq _ from to-from from-to where
    to = FreeAbelianGroup-extend
    from = f*

    to-from : ∀ h → to (from h) == h
    to-from h = group-hom= $ λ= $ FormalSum-elim
      (λ _ → =-preserves-set G.El-level)
      (λ l → Word-extend-hom h l)
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
