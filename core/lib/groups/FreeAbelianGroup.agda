{-# OPTIONS --without-K --rewriting #-}

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
open import lib.groups.GroupProduct
open import lib.groups.Homomorphism
open import lib.groups.Isomorphism

module lib.groups.FreeAbelianGroup {i} where

-- the relation for making the quotient.

-- [fsr-sym] is not needed, but it seems more principled to
-- make [FormalSumRel] an equivalence relation.
data FormalSumRel {A : Type i} : Word A → Word A → Type i where
  fsr-refl : ∀ {l₁ l₂} → l₁ == l₂ → FormalSumRel l₁ l₂
  fsr-trans : ∀ {l₁ l₂ l₃} → FormalSumRel l₁ l₂ → FormalSumRel l₂ l₃ → FormalSumRel l₁ l₃
  fsr-sym : ∀ {l₁ l₂} → FormalSumRel l₁ l₂ → FormalSumRel l₂ l₁
  fsr-cons : ∀ x {l₁ l₂} → FormalSumRel l₁ l₂ → FormalSumRel (x :: l₁) (x :: l₂)
  fsr-swap : ∀ x₁ x₂ l → FormalSumRel (x₁ :: x₂ :: l) (x₂ :: x₁ :: l)
  fsr-flip : ∀ x₁ l → FormalSumRel (x₁ :: flip x₁ :: l) l

-- The quotient
FormalSum : Type i → Type i
FormalSum A = SetQuot (FormalSumRel {A})

module _ {A : Type i} where

  fs[_] : Word A → FormalSum A
  fs[_] = q[_]

  FormalSum-level : is-set (FormalSum A)
  FormalSum-level = SetQuot-level

  FormalSum-is-set = FormalSum-level

  module FormalSumElim {k} {P : FormalSum A → Type k}
    (p : (x : FormalSum A) → is-set (P x)) (incl* : (a : Word A) → P fs[ a ])
    (rel* : ∀ {a₁ a₂} (r : FormalSumRel a₁ a₂) → incl* a₁ == incl* a₂ [ P ↓ quot-rel r ])
    = SetQuotElim p incl* rel*
  open FormalSumElim public using () renaming (f to FormalSum-elim)

  module FormalSumRec {k} {B : Type k} (p : is-set B) (incl* : Word A → B)
    (rel* : ∀ {a₁ a₂} (r : FormalSumRel a₁ a₂) → incl* a₁ == incl* a₂)
    = SetQuotRec p incl* rel*
  open FormalSumRec public using () renaming (f to FormalSum-rec)

module _ {A : Type i} where
  -- useful properties that remain public
  abstract
    FormalSumRel-cong-++-l :
      ∀ {l₁ l₁'} → FormalSumRel {A} l₁ l₁'
      → (l₂ : Word A)
      → FormalSumRel (l₁ ++ l₂) (l₁' ++ l₂)
    FormalSumRel-cong-++-l (fsr-refl idp) l₂ = fsr-refl idp
    FormalSumRel-cong-++-l (fsr-trans fsr₁ fsr₂) l₂ = fsr-trans (FormalSumRel-cong-++-l fsr₁ l₂) (FormalSumRel-cong-++-l fsr₂ l₂)
    FormalSumRel-cong-++-l (fsr-sym fsr) l₂ = fsr-sym (FormalSumRel-cong-++-l fsr l₂)
    FormalSumRel-cong-++-l (fsr-cons x fsr₁) l₂ = fsr-cons x (FormalSumRel-cong-++-l fsr₁ l₂)
    FormalSumRel-cong-++-l (fsr-swap x₁ x₂ l₁) l₂ = fsr-swap x₁ x₂ (l₁ ++ l₂)
    FormalSumRel-cong-++-l (fsr-flip x₁ l₁) l₂ = fsr-flip x₁ (l₁ ++ l₂)

    FormalSumRel-cong-++-r :
      ∀ (l₁ : Word A)
      → ∀ {l₂ l₂'} → FormalSumRel l₂ l₂'
      → FormalSumRel (l₁ ++ l₂) (l₁ ++ l₂')
    FormalSumRel-cong-++-r nil fsr₂ = fsr₂
    FormalSumRel-cong-++-r (x :: l₁) fsr₂ = fsr-cons x (FormalSumRel-cong-++-r l₁ fsr₂)

    FormalSumRel-swap1 : ∀ x l₁ l₂ → FormalSumRel {A} (l₁ ++ (x :: l₂)) (x :: l₁ ++ l₂)
    FormalSumRel-swap1 x nil l₂ = fsr-refl idp
    FormalSumRel-swap1 x (x₁ :: l₁) l₂ = fsr-trans (fsr-cons x₁ (FormalSumRel-swap1 x l₁ l₂)) (fsr-swap x₁ x (l₁ ++ l₂))

module _ (A : Type i) where
  private
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
      FormalSumRel-cong-flip (fsr-sym fsr) = fsr-sym (FormalSumRel-cong-flip fsr)
      FormalSumRel-cong-flip (fsr-cons x fsr₁) = fsr-cons (flip x) (FormalSumRel-cong-flip fsr₁)
      FormalSumRel-cong-flip (fsr-swap x₁ x₂ l) = fsr-swap (flip x₁) (flip x₂) (Word-flip l)
      FormalSumRel-cong-flip (fsr-flip (inl x) l) = fsr-flip (inr x) (Word-flip l)
      FormalSumRel-cong-flip (fsr-flip (inr x) l) = fsr-flip (inl x) (Word-flip l)

    ⊟ : FormalSum A → FormalSum A
    ⊟ = FormalSum-rec FormalSum-is-set (fs[_] ∘ Word-flip)
      (λ r → quot-rel $ FormalSumRel-cong-flip r)

    ⊞-unit : FormalSum A
    ⊞-unit = fs[ nil ]

    abstract
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

  FreeAbGroup : AbGroup i
  FreeAbGroup = group _ FormalSum-is-set FormalSum-group-structure , ⊞-comm

  module FreeAbGroup = AbGroup FreeAbGroup

{- Freeness (universal properties) -}

module _ {A : Type i} {j} (G : AbGroup j) where

  private
    module G = AbGroup G

    abstract
      Word-extendᴳ-emap : ∀ f {l₁ l₂}
        → FormalSumRel {A} l₁ l₂
        → Word-extendᴳ G.grp f l₁ == Word-extendᴳ G.grp f l₂
      Word-extendᴳ-emap f (fsr-refl idp) = idp
      Word-extendᴳ-emap f (fsr-trans fsr fsr₁) = (Word-extendᴳ-emap f fsr) ∙ (Word-extendᴳ-emap f fsr₁)
      Word-extendᴳ-emap f (fsr-sym fsr) = ! (Word-extendᴳ-emap f fsr)
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

  FormalSum-extend : (A → G.El) → FormalSum A → G.El
  FormalSum-extend f = FormalSum-rec G.El-level (Word-extendᴳ G.grp f)
    (λ r → Word-extendᴳ-emap f r)

  FreeAbGroup-extend : (A → G.El) → (FreeAbGroup.grp A →ᴳ G.grp)
  FreeAbGroup-extend f' = record {M} where
    module M where
      f : FreeAbGroup.El A → G.El
      f = FormalSum-extend f'
      abstract
        pres-comp : preserves-comp (FreeAbGroup.comp A) G.comp f
        pres-comp =
          FormalSum-elim (λ _ → Π-is-set λ _ → =-preserves-set G.El-level)
            (λ l₁ → FormalSum-elim
              (λ _ → =-preserves-set G.El-level)
              (λ l₂ → Word-extendᴳ-++ G.grp f' l₁ l₂)
              (λ _ → prop-has-all-paths-↓ (G.El-level _ _)))
            (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → G.El-level _ _))

  private
    module Lemma (hom : FreeAbGroup.grp A →ᴳ G.grp) where
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

  FreeAbGroup-extend-is-equiv : is-equiv FreeAbGroup-extend
  FreeAbGroup-extend-is-equiv = is-eq _ from to-from from-to where
    to = FreeAbGroup-extend
    from = f*

    abstract
      to-from : ∀ h → to (from h) == h
      to-from h = group-hom= $ λ= $ FormalSum-elim
        (λ _ → =-preserves-set G.El-level)
        (λ l → Word-extend-hom h l)
        (λ _ → prop-has-all-paths-↓ (G.El-level _ _))

      from-to : ∀ f → from (to f) == f
      from-to f = λ= λ a → G.unit-r (f a)

  FreeAbGroup-extend-hom : Πᴳ A (λ _ → G.grp) →ᴳ hom-group (FreeAbGroup.grp A) G
  FreeAbGroup-extend-hom = record {M} where
    module M where
      f : (A → G.El) → (FreeAbGroup.grp A →ᴳ G.grp)
      f = FreeAbGroup-extend
      abstract
        pres-comp : preserves-comp (Group.comp (Πᴳ A (λ _ → G.grp))) (Group.comp (hom-group (FreeAbGroup.grp A) G)) f
        pres-comp = λ f₁ f₂ → group-hom= $ λ= $
          FormalSum-elim (λ _ → =-preserves-set G.El-is-set)
            (Word-extendᴳ-comp G f₁ f₂)
            (λ _ → prop-has-all-paths-↓ (G.El-is-set _ _))

  FreeAbGroup-extend-iso : Πᴳ A (λ _ → G.grp) ≃ᴳ hom-group (FreeAbGroup.grp A) G
  FreeAbGroup-extend-iso = FreeAbGroup-extend-hom , FreeAbGroup-extend-is-equiv
