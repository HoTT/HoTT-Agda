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
open import lib.groups.Homomorphism

module lib.groups.FreeGroup {i} where

-- [qwr-sym] is not needed, but it seems more principled to
-- make [QuotWordRel] an equivalence relation.
data QuotWordRel {A : Type i} : Word A → Word A → Type i where
  qwr-refl : ∀ {l₁ l₂} → l₁ == l₂ → QuotWordRel l₁ l₂
  qwr-trans : ∀ {l₁ l₂ l₃} → QuotWordRel l₁ l₂ → QuotWordRel l₂ l₃ → QuotWordRel l₁ l₃
  qwr-sym : ∀ {l₁ l₂} → QuotWordRel l₁ l₂ → QuotWordRel l₂ l₁
  qwr-cons : ∀ x {l₁ l₂} → QuotWordRel l₁ l₂ → QuotWordRel (x :: l₁) (x :: l₂)
  qwr-flip : ∀ x₁ l → QuotWordRel (x₁ :: flip x₁ :: l) l

-- The quotient
QuotWord : Type i → Type i
QuotWord A = SetQuot (QuotWordRel {A})

module _ {A : Type i} where

  qw[_] : Word A → QuotWord A
  qw[_] = q[_]

  QuotWord-level : is-set (QuotWord A)
  QuotWord-level = SetQuot-level

  QuotWord-is-set = QuotWord-level

  module QuotWordElim {k} {P : QuotWord A → Type k}
    (p : (x : QuotWord A) → is-set (P x)) (incl* : (a : Word A) → P qw[ a ])
    (rel* : ∀ {a₁ a₂} (r : QuotWordRel a₁ a₂) → incl* a₁ == incl* a₂ [ P ↓ quot-rel r ])
    = SetQuotElim p incl* rel*
  open QuotWordElim public renaming (f to QuotWord-elim) hiding (quot-rel-β)

  module QuotWordRec {k} {B : Type k} (p : is-set B) (incl* : Word A → B)
    (rel* : ∀ {a₁ a₂} (r : QuotWordRel a₁ a₂) → incl* a₁ == incl* a₂)
    = SetQuotRec p incl* rel*
  open QuotWordRec public renaming (f to QuotWord-rec)

module _ (A : Type i) where
  private
    abstract
      QuotWordRel-cong-++-l :
        ∀ {l₁ l₁'} → QuotWordRel {A} l₁ l₁'
        → (l₂ : Word A)
        → QuotWordRel (l₁ ++ l₂) (l₁' ++ l₂)
      QuotWordRel-cong-++-l (qwr-refl idp) l₂ = qwr-refl idp
      QuotWordRel-cong-++-l (qwr-trans qwr₁ qwr₂) l₂ = qwr-trans (QuotWordRel-cong-++-l qwr₁ l₂) (QuotWordRel-cong-++-l qwr₂ l₂)
      QuotWordRel-cong-++-l (qwr-sym qwr) l₂ = qwr-sym (QuotWordRel-cong-++-l qwr l₂)
      QuotWordRel-cong-++-l (qwr-cons x qwr₁) l₂ = qwr-cons x (QuotWordRel-cong-++-l qwr₁ l₂)
      QuotWordRel-cong-++-l (qwr-flip x₁ l₁) l₂ = qwr-flip x₁ (l₁ ++ l₂)

      QuotWordRel-cong-++-r :
        ∀ (l₁ : Word A)
        → ∀ {l₂ l₂'} → QuotWordRel l₂ l₂'
        → QuotWordRel (l₁ ++ l₂) (l₁ ++ l₂')
      QuotWordRel-cong-++-r nil qwr₂ = qwr₂
      QuotWordRel-cong-++-r (x :: l₁) qwr₂ = qwr-cons x (QuotWordRel-cong-++-r l₁ qwr₂)

    infixl 80 _⊞_
    _⊞_ : QuotWord A → QuotWord A → QuotWord A
    _⊞_ = QuotWord-rec
      (→-is-set QuotWord-is-set)
      (λ l₁ → QuotWord-rec QuotWord-is-set (λ l₂ → qw[ l₁ ++ l₂ ])
        (λ r → quot-rel $ QuotWordRel-cong-++-r l₁ r))
      (λ {l₁} {l₁'} r → λ= $ QuotWord-elim
        (λ _ → =-preserves-set QuotWord-is-set)
        (λ l₂ → quot-rel $ QuotWordRel-cong-++-l r l₂)
        (λ _ → prop-has-all-paths-↓ (QuotWord-is-set _ _)))

    abstract
      QuotWordRel-cong-flip : ∀ {l₁ l₂}
        → QuotWordRel {A} l₁ l₂ → QuotWordRel (Word-flip l₁) (Word-flip l₂)
      QuotWordRel-cong-flip (qwr-refl idp) = qwr-refl idp
      QuotWordRel-cong-flip (qwr-trans qwr₁ qwr₂) = qwr-trans (QuotWordRel-cong-flip qwr₁) (QuotWordRel-cong-flip qwr₂)
      QuotWordRel-cong-flip (qwr-sym qwr) = qwr-sym (QuotWordRel-cong-flip qwr)
      QuotWordRel-cong-flip (qwr-cons x qwr₁) = qwr-cons (flip x) (QuotWordRel-cong-flip qwr₁)
      QuotWordRel-cong-flip (qwr-flip (inl x) l) = qwr-flip (inr x) (Word-flip l)
      QuotWordRel-cong-flip (qwr-flip (inr x) l) = qwr-flip (inl x) (Word-flip l)

      QuotWordRel-cong-reverse : ∀ {l₁ l₂}
        → QuotWordRel {A} l₁ l₂ → QuotWordRel (reverse l₁) (reverse l₂)
      QuotWordRel-cong-reverse (qwr-refl x) = qwr-refl (ap reverse x)
      QuotWordRel-cong-reverse (qwr-trans qwr qwr₁) = qwr-trans (QuotWordRel-cong-reverse qwr) (QuotWordRel-cong-reverse qwr₁)
      QuotWordRel-cong-reverse (qwr-sym qwr) = qwr-sym (QuotWordRel-cong-reverse qwr)
      QuotWordRel-cong-reverse (qwr-cons x qwr) = QuotWordRel-cong-++-l (QuotWordRel-cong-reverse qwr) (x :: nil)
      QuotWordRel-cong-reverse (qwr-flip (inl x) l) =
        qwr-trans (qwr-refl (++-assoc (reverse l) (inr x :: nil) (inl x :: nil))) $
        qwr-trans (QuotWordRel-cong-++-r (reverse l) (qwr-flip (inr x) nil)) $
        qwr-refl (++-unit-r (reverse l))
      QuotWordRel-cong-reverse (qwr-flip (inr x) l) =
        qwr-trans (qwr-refl (++-assoc (reverse l) (inl x :: nil) (inr x :: nil))) $
        qwr-trans (QuotWordRel-cong-++-r (reverse l) (qwr-flip (inl x) nil)) $
        qwr-refl (++-unit-r (reverse l))

    ⊟ : QuotWord A → QuotWord A
    ⊟ = QuotWord-rec QuotWord-is-set (qw[_] ∘ reverse ∘ Word-flip)
      (λ r → quot-rel $ QuotWordRel-cong-reverse $ QuotWordRel-cong-flip r)

    ⊞-unit : QuotWord A
    ⊞-unit = qw[ nil ]

    abstract
      ⊞-unit-l : ∀ g → ⊞-unit ⊞ g == g
      ⊞-unit-l = QuotWord-elim
        (λ _ → =-preserves-set QuotWord-is-set)
        (λ _ → idp)
        (λ _ → prop-has-all-paths-↓ (QuotWord-is-set _ _))

      ⊞-unit-r : ∀ g → g ⊞ ⊞-unit == g
      ⊞-unit-r = QuotWord-elim
        (λ _ → =-preserves-set QuotWord-is-set)
        (λ _ → ap qw[_] $ ++-unit-r _)
        (λ _ → prop-has-all-paths-↓ (QuotWord-is-set _ _))

      ⊞-assoc : ∀ g₁ g₂ g₃ → (g₁ ⊞ g₂) ⊞ g₃ == g₁ ⊞ (g₂ ⊞ g₃)
      ⊞-assoc = QuotWord-elim (λ _ → Π-is-set λ _ → Π-is-set λ _ → =-preserves-set QuotWord-is-set)
        (λ l₁ → QuotWord-elim (λ _ → Π-is-set λ _ → =-preserves-set QuotWord-is-set)
          (λ l₂ → QuotWord-elim (λ _ → =-preserves-set QuotWord-is-set)
            (λ l₃ → ap qw[_] $ ++-assoc l₁ l₂ l₃)
            (λ _ → prop-has-all-paths-↓ $ QuotWord-is-set _ _))
          (λ _ → prop-has-all-paths-↓ $ Π-is-prop λ _ → QuotWord-is-set _ _))
        (λ _ → prop-has-all-paths-↓ $ Π-is-prop λ _ → Π-is-prop λ _ → QuotWord-is-set _ _)

      Word-inv-r : ∀ l → QuotWordRel {A} (l ++ reverse (Word-flip l)) nil
      Word-inv-r nil = qwr-refl idp
      Word-inv-r (x :: l) =
        qwr-trans (qwr-refl (ap (x ::_) (! (++-assoc l (reverse (Word-flip l)) (flip x :: nil))))) $
        qwr-trans (qwr-cons x (QuotWordRel-cong-++-l (Word-inv-r l) (flip x :: nil))) $
        qwr-flip x nil

      ⊟-inv-r : ∀ g → g ⊞ (⊟ g) == ⊞-unit
      ⊟-inv-r = QuotWord-elim
        (λ _ → =-preserves-set QuotWord-is-set)
        (λ l → quot-rel (Word-inv-r l))
        (λ _ → prop-has-all-paths-↓ (QuotWord-is-set _ _))

      Word-inv-l : ∀ l → QuotWordRel {A} (reverse (Word-flip l) ++ l) nil
      Word-inv-l nil = qwr-refl idp
      Word-inv-l (inl x :: l) =
        qwr-trans (qwr-refl (++-assoc (reverse (Word-flip l)) (inr x :: nil) (inl x :: l))) $
        qwr-trans (QuotWordRel-cong-++-r (reverse (Word-flip l)) (qwr-flip (inr x) l)) $
        Word-inv-l l
      Word-inv-l (inr x :: l) =
        qwr-trans (qwr-refl (++-assoc (reverse (Word-flip l)) (inl x :: nil) (inr x :: l))) $
        qwr-trans (QuotWordRel-cong-++-r (reverse (Word-flip l)) (qwr-flip (inl x) l)) $
        Word-inv-l l

      ⊟-inv-l : ∀ g → (⊟ g) ⊞ g == ⊞-unit
      ⊟-inv-l = QuotWord-elim
        (λ _ → =-preserves-set QuotWord-is-set)
        (λ l → quot-rel (Word-inv-l l))
        (λ _ → prop-has-all-paths-↓ (QuotWord-is-set _ _))

  QuotWord-group-structure : GroupStructure (QuotWord A)
  QuotWord-group-structure = record
    { ident = ⊞-unit
    ; inv = ⊟
    ; comp = _⊞_
    ; unit-l = ⊞-unit-l
    ; unit-r = ⊞-unit-r
    ; assoc = ⊞-assoc
    ; inv-r = ⊟-inv-r
    ; inv-l = ⊟-inv-l
    }

  FreeGroup : Group i
  FreeGroup = group _ QuotWord-is-set QuotWord-group-structure

  module FreeGroup = Group FreeGroup

-- freeness
module _ {A : Type i} {j} (G : Group j) where

  private
    module G = Group G

    abstract
      Word-extendᴳ-emap : ∀ f {l₁ l₂}
        → QuotWordRel {A} l₁ l₂
        → Word-extendᴳ G f l₁ == Word-extendᴳ G f l₂
      Word-extendᴳ-emap f (qwr-refl idp) = idp
      Word-extendᴳ-emap f (qwr-trans qwr qwr₁) = (Word-extendᴳ-emap f qwr) ∙ (Word-extendᴳ-emap f qwr₁)
      Word-extendᴳ-emap f (qwr-sym qwr) = ! (Word-extendᴳ-emap f qwr)
      Word-extendᴳ-emap f (qwr-cons x qwr) = ap (G.comp (PlusMinus-extendᴳ G f x)) (Word-extendᴳ-emap f qwr)
      Word-extendᴳ-emap f (qwr-flip (inl x) l) =
          ! (G.assoc (f x) (G.inv (f x)) (Word-extendᴳ G f l))
        ∙ ap (λ g → G.comp g (Word-extendᴳ G f l)) (G.inv-r (f x)) ∙ G.unit-l _
      Word-extendᴳ-emap f (qwr-flip (inr x) l) =
          ! (G.assoc (G.inv (f x)) (f x) (Word-extendᴳ G f l))
        ∙ ap (λ g → G.comp g (Word-extendᴳ G f l)) (G.inv-l (f x)) ∙ G.unit-l _

  FreeGroup-extend : (A → G.El) → (FreeGroup A →ᴳ G)
  FreeGroup-extend f' = record {M} where
    module M where
      f : QuotWord A → G.El
      f = QuotWord-rec G.El-level (Word-extendᴳ G f')
          (λ r → Word-extendᴳ-emap f' r)
      abstract
        pres-comp : preserves-comp (FreeGroup.comp A) G.comp f
        pres-comp =
          QuotWord-elim (λ _ → Π-is-set λ _ → =-preserves-set G.El-level)
            (λ l₁ → QuotWord-elim
              (λ _ → =-preserves-set G.El-level)
              (λ l₂ → Word-extendᴳ-++ G f' l₁ l₂)
              (λ _ → prop-has-all-paths-↓ (G.El-level _ _)))
            (λ _ → prop-has-all-paths-↓ (Π-is-prop λ _ → G.El-level _ _))

  private
    module Lemma (hom : FreeGroup A →ᴳ G) where
      open GroupHom hom
      f* : A → G.El
      f* a = f qw[ inl a :: nil ]

      abstract
        PlusMinus-extendᴳ-hom : ∀ x → PlusMinus-extendᴳ G f* x == f qw[ x :: nil ]
        PlusMinus-extendᴳ-hom (inl x) = idp
        PlusMinus-extendᴳ-hom (inr x) = ! $ pres-inv qw[ inl x :: nil ]

        Word-extendᴳ-hom : ∀ l → Word-extendᴳ G f* l == f qw[ l ]
        Word-extendᴳ-hom nil = ! pres-ident
        Word-extendᴳ-hom (x :: l) = ap2 G.comp (PlusMinus-extendᴳ-hom x) (Word-extendᴳ-hom l) ∙ ! (pres-comp _ _)
    open Lemma

  FreeGroup-extend-is-equiv : is-equiv FreeGroup-extend
  FreeGroup-extend-is-equiv = is-eq _ from to-from from-to where
    to = FreeGroup-extend
    from = f*

    abstract
      to-from : ∀ h → to (from h) == h
      to-from h = group-hom= $ λ= $ QuotWord-elim
        (λ _ → =-preserves-set G.El-level)
        (λ l → Word-extendᴳ-hom h l)
        (λ _ → prop-has-all-paths-↓ (G.El-level _ _))

      from-to : ∀ f → from (to f) == f
      from-to f = λ= λ a → G.unit-r (f a)
