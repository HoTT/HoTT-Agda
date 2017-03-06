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
ℤ-group = group _ ℤ-is-set ℤ-group-structure

ℤ-group-is-abelian : is-abelian ℤ-group
ℤ-group-is-abelian = ℤ+-comm

ℤ-abgroup : AbGroup₀
ℤ-abgroup = ℤ-group , ℤ-group-is-abelian

ℤ-iso-FreeAbGroup-Unit : ℤ-group ≃ᴳ FreeAbGroup.grp Unit
ℤ-iso-FreeAbGroup-Unit = ≃-to-≃ᴳ (equiv to from to-from from-to) to-pres-comp where
  to = FreeAbGroup.exp Unit fs[ inl unit :: nil ]
  from = FormalSum-extend ℤ-abgroup (λ _ → 1)
  abstract
    to-pres-comp = FreeAbGroup.exp-+ Unit fs[ inl unit :: nil ]

    to-from' : ∀ l → to (Word-extendᴳ ℤ-group (λ _ → 1) l) == fs[ l ]
    to-from' nil = idp
    to-from' (inl unit :: l) =
        FreeAbGroup.exp-succ Unit fs[ inl unit :: nil ] (Word-extendᴳ ℤ-group (λ _ → 1) l)
      ∙ ap (FreeAbGroup.comp Unit fs[ inl unit :: nil ]) (to-from' l)
    to-from' (inr unit :: l) =
        FreeAbGroup.exp-pred Unit fs[ inl unit :: nil ] (Word-extendᴳ ℤ-group (λ _ → 1) l)
      ∙ ap (FreeAbGroup.comp Unit fs[ inr unit :: nil ]) (to-from' l)

    to-from : ∀ fs → to (from fs) == fs
    to-from = FormalSum-elim (λ _ → =-preserves-set FormalSum-level)
      to-from' (λ _ → prop-has-all-paths-↓ (FormalSum-level _ _))

    from-to : ∀ z → from (to z) == z
    from-to (pos 0) = idp
    from-to (pos 1) = idp
    from-to (negsucc 0) = idp
    from-to (pos (S (S n))) =
        GroupHom.pres-comp (FreeAbGroup-extend ℤ-abgroup (λ _ → 1))
          fs[ inl unit :: nil ] (FreeAbGroup.exp Unit fs[ inl unit :: nil ] (pos (S n)))
      ∙ ap succ (from-to (pos (S n)))
    from-to (negsucc (S n)) =
        GroupHom.pres-comp (FreeAbGroup-extend ℤ-abgroup (λ _ → 1))
          fs[ inr unit :: nil ] (FreeAbGroup.exp Unit fs[ inl unit :: nil ] (negsucc n))
      ∙ ap pred (from-to (negsucc n))
