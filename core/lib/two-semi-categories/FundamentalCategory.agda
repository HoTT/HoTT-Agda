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
      ; assoc = ∙-assoc
      ; pentagon-identity = ∙-assoc-pentagon
      }
    }

  =ₜ-fundamental-cat : TwoSemiCategory i i
  =ₜ-fundamental-cat =
    record
    { El = Trunc 2 A
    ; Arr = _=ₜ_
    ; Arr-level = =ₜ-level
    ; two-semi-cat-struct = record
      { comp = λ {ta} → _∙ₜ_ {ta = ta}
      ; assoc = λ {ta} → ∙ₜ-assoc {ta = ta}
      ; pentagon-identity = λ {ta} → ∙ₜ-assoc-pentagon {ta = ta}
      }
    }

module _ {i} (A : Type i) where

  2-type-to-=ₜ-fundamental-cat :
    TwoSemiFunctor (2-type-fundamental-cat (Trunc 2 A))
                   (=ₜ-fundamental-cat A)
  2-type-to-=ₜ-fundamental-cat =
    record
    { F₀ = idf (Trunc 2 A)
    ; F₁ = λ {ta} {tb} → –> (=ₜ-equiv ta tb)
    ; pres-comp = –>-=ₜ-equiv-pres-∙
      -- TODO: The following line takes a really long time to check.
      -- Can we optimize this somehow?
    ; pres-comp-coh = λ {ta} → –>-=ₜ-equiv-pres-∙-coh {ta = ta}
    }

  private
    module FunctorInv =
      FunctorInverse 2-type-to-=ₜ-fundamental-cat
                     (idf-is-equiv (Trunc 2 A))
                     (λ ta tb → snd (=ₜ-equiv ta tb))
    module InvFunctor = TwoSemiFunctor FunctorInv.functor

  =ₜ-to-2-type-fundamental-cat :
    TwoSemiFunctor (=ₜ-fundamental-cat A)
                   (2-type-fundamental-cat (Trunc 2 A))
  =ₜ-to-2-type-fundamental-cat =
    record
    { F₀ = idf (Trunc 2 A)
    ; F₁ = λ {ta} {tb} → <– (=ₜ-equiv ta tb)
    ; pres-comp = InvFunctor.pres-comp
    ; pres-comp-coh = InvFunctor.pres-comp-coh
    }

  module =ₜ-to-2-type-fundamental-cat = TwoSemiFunctor =ₜ-to-2-type-fundamental-cat

  =ₜ-to-2-type-fundamental-cat-pres-comp-β : {a b c : A}
    (p : a == b) (q : b == c)
    → =ₜ-to-2-type-fundamental-cat.pres-comp {x = [ a ]} {y = [ b ]} {z = [ c ]} [ p ]₁ [ q ]₁
      == ap-∙ [_] p q
  =ₜ-to-2-type-fundamental-cat-pres-comp-β {a} p@idp q@idp = =ₛ-out $
    =ₜ-to-2-type-fundamental-cat.pres-comp {[ a ]} {[ b ]} {[ c ]} [ p ]₁ [ q ]₁ ◃∎
      =ₛ⟨ FunctorInv.pres-comp-β {[ a ]} {[ b ]} {[ c ]} [ p ]₁ [ q ]₁ ⟩
    idp ◃∙
    idp ◃∙
    ap-∙ [_] p q ◃∙
    idp ◃∎
      =ₛ⟨ 0 & 1 & expand [] ⟩
    idp ◃∙
    ap-∙ [_] p q ◃∙
    idp ◃∎
      =ₛ⟨ 0 & 1 & expand [] ⟩
    ap-∙ [_] p q ◃∙
    idp ◃∎
      =ₛ⟨ 1 & 1 & expand [] ⟩
    ap-∙ [_] p q ◃∎ ∎ₛ
    where
      b = a
      c = a
      module C = TwoSemiCategory (2-type-fundamental-cat (Trunc 2 A))
      module D = TwoSemiCategory (=ₜ-fundamental-cat A)


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
