{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Int
open import lib.types.Group
open import lib.types.List
open import lib.types.Word
open import lib.groups.Homomorphism
open import lib.groups.Isomorphism
open import lib.groups.FreeAbelianGroup
open import lib.groups.GeneratedGroup
open import lib.types.SetQuotient

module lib.groups.Int where

ℤ-group-structure : GroupStructure ℤ
ℤ-group-structure = record
  { ident = 0
  ; inv = ℤ~
  ; comp = _ℤ+_
  ; unit-l = ℤ+-unit-l
  ; assoc = ℤ+-assoc
  ; inv-l = ℤ~-inv-l
  }

ℤ-group : Group₀
ℤ-group = group _ ℤ-group-structure

ℤ-group-is-abelian : is-abelian ℤ-group
ℤ-group-is-abelian = ℤ+-comm

ℤ-abgroup : AbGroup₀
ℤ-abgroup = ℤ-group , ℤ-group-is-abelian

private
  module OneGeneratorFreeAbGroup = FreeAbelianGroup Unit

OneGenFreeAbGroup : AbGroup lzero
OneGenFreeAbGroup = OneGeneratorFreeAbGroup.FreeAbGroup

private
  module OneGenFreeAbGroup = AbGroup OneGenFreeAbGroup

ℤ-iso-FreeAbGroup-Unit : ℤ-group ≃ᴳ OneGenFreeAbGroup.grp
ℤ-iso-FreeAbGroup-Unit = ≃-to-≃ᴳ (equiv to from to-from from-to) to-pres-comp where
  open OneGeneratorFreeAbGroup
  module F = Freeness ℤ-abgroup
  to : Group.El ℤ-group → OneGenFreeAbGroup.El
  to = OneGenFreeAbGroup.exp qw[ inl unit :: nil ]
  from : OneGenFreeAbGroup.El → Group.El ℤ-group
  from = GroupHom.f (F.extend (λ _ → 1))
  abstract
    to-pres-comp = OneGenFreeAbGroup.exp-+ qw[ inl unit :: nil ]

    to-from' : ∀ l → to (Word-extendᴳ ℤ-group (λ _ → 1) l) == qw[ l ]
    to-from' nil = idp
    to-from' (inl unit :: nil) = idp
    to-from' (inl unit :: l@(_ :: _)) =
        OneGenFreeAbGroup.exp-succ qw[ inl unit :: nil ] (Word-extendᴳ ℤ-group (λ _ → 1) l)
      ∙ ap (OneGenFreeAbGroup.comp qw[ inl unit :: nil ]) (to-from' l)
    to-from' (inr unit :: nil) = idp
    to-from' (inr unit :: l@(_ :: _)) =
        OneGenFreeAbGroup.exp-pred qw[ inl unit :: nil ] (Word-extendᴳ ℤ-group (λ _ → 1) l)
      ∙ ap (OneGenFreeAbGroup.comp qw[ inr unit :: nil ]) (to-from' l)

    to-from : ∀ fs → to (from fs) == fs
    to-from = QuotWord-elim to-from' (λ _ → prop-has-all-paths-↓)

    from-to : ∀ z → from (to z) == z
    from-to (pos 0) = idp
    from-to (pos 1) = idp
    from-to (negsucc 0) = idp
    from-to (pos (S (S n))) =
        GroupHom.pres-comp (F.extend (λ _ → 1))
          qw[ inl unit :: nil ] (OneGenFreeAbGroup.exp qw[ inl unit :: nil ] (pos (S n)))
      ∙ ap succ (from-to (pos (S n)))
    from-to (negsucc (S n)) =
        GroupHom.pres-comp (F.extend (λ _ → 1))
          qw[ inr unit :: nil ] (OneGenFreeAbGroup.exp qw[ inl unit :: nil ] (negsucc n))
      ∙ ap pred (from-to (negsucc n))

exp-shom : ∀ {i} {GEl : Type i} (GS : GroupStructure GEl) (g : GEl) → ℤ-group-structure →ᴳˢ GS
exp-shom GS g = group-structure-hom (GroupStructure.exp GS g) (GroupStructure.exp-+ GS g)

exp-hom : ∀ {i} (G : Group i) (g : Group.El G) → ℤ-group →ᴳ G
exp-hom G g = group-hom (Group.exp G g) (Group.exp-+ G g)
