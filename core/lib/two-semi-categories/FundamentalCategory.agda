{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Truncation
open import lib.types.TwoSemiCategory
open import lib.two-semi-categories.Functor
open import lib.two-semi-categories.FunctorInverse
open import lib.two-semi-categories.GroupToCategory

module lib.two-semi-categories.FundamentalCategory where

module _ {i} (A : Type i) where

  2-type-fundamental-cat : {{_ : has-level 2 A}} → TwoSemiCategory i i
  2-type-fundamental-cat =
    record
    { El = A
    ; Arr = _==_
    ; Arr-level = λ _ _ → ⟨⟩
    ; two-semi-cat-struct = record
      { comp = _∙_
      ; assoc = λ a b c → ∙-assoc a b c
      ; pentagon-identity = λ p q r s → =ₛ-in (∙-assoc-pentagon p q r s)
      }
    }

  =ₜ-fundamental-cat : TwoSemiCategory i i
  =ₜ-fundamental-cat =
    record
    { El = Trunc 2 A
    ; Arr = _=ₜ_
    ; Arr-level = =ₜ-level
    ; two-semi-cat-struct = record
      { comp = λ {ta} p q → _∙ₜ_ {ta = ta} p q
      ; assoc = λ {ta} p q r → ∙ₜ-assoc {ta = ta} p q r
      ; pentagon-identity = λ {ta} p q r s → =ₛ-in (∙ₜ-assoc-pentagon {ta = ta} p q r s)
      }
    }

module _ {i} (A : Type i) where

  2-type-to-=ₜ-fundamental-cat :
    TwoSemiFunctor (2-type-fundamental-cat (Trunc 2 A))
                   (=ₜ-fundamental-cat A)
  2-type-to-=ₜ-fundamental-cat =
    record
    { F₀ = idf (Trunc 2 A)
    ; F₁ = λ {ta} {tb} f → –> (=ₜ-equiv ta tb) f
    ; pres-comp = –>-=ₜ-equiv-pres-∙
      -- TODO: The following line takes a really long time to check
      -- Can we optimize this somehow?
    ; pres-comp-coh = λ {ta} p q r → =ₛ-in $ –>-=ₜ-equiv-pres-∙-coh {ta = ta} p q r
    }

  =ₜ-to-2-type-fundamental-cat :
    TwoSemiFunctor (=ₜ-fundamental-cat A)
                   (2-type-fundamental-cat (Trunc 2 A))
  =ₜ-to-2-type-fundamental-cat =
    functor-inverse 2-type-to-=ₜ-fundamental-cat
      (idf-is-equiv (Trunc 2 A))
      (λ ta tb → snd (=ₜ-equiv ta tb))

  =ₜ-to-2-type-fundamental-cat-F₁ : ∀ {ta} {tb} (p : ta =ₜ tb)
    → TwoSemiFunctor.F₁ =ₜ-to-2-type-fundamental-cat p == <– (=ₜ-equiv ta tb) p
  =ₜ-to-2-type-fundamental-cat-F₁ p = idp

module _ {i} (C : Type i) (c₀ : C) {{C-level : has-level 1 C}} where

  open import lib.groups.LoopSpace

  fundamental-group-to-fundamental-groupoid :
    TwoSemiFunctor (group-to-cat (Ω^S-group 0 ⊙[ C , c₀ ]))
                   (2-type-fundamental-cat C {{raise-level 1 C-level}})
  fundamental-group-to-fundamental-groupoid =
    record
    { F₀ = λ _ → c₀
    ; F₁ = λ p → p
    ; pres-comp = λ p q → idp
    ; pres-comp-coh =
        λ p q r → =ₛ-in $
          prop-path (has-level-apply (has-level-apply C-level _ _) _ _) _ _
    }
