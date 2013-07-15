{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.HSpace

module homotopy.CircleHSpace where

open S¹Rec using (loop-β) renaming (f to S¹-rec)

S¹-hSpace : HSpaceStructure S¹
S¹-hSpace = hSpaceStructure base μ μe- μ-e where

  turn-around : (x : S¹) → x == x
  turn-around = S¹-elim loop (↓-idf=idf-in (∙=∙' loop loop))

  μ : S¹ → S¹ → S¹
  μ = S¹-rec (idf S¹) (λ= turn-around)

  μe- : (x : S¹) → μ base x == x
  μe- x = idp

  μ-e : (x : S¹) → μ x base == x
  μ-e = S¹-elim idp (↓-app=idf-in
    (idp ∙' loop                          =⟨ ∙'-unit-l loop ⟩
     loop                                 =⟨ idp ⟩
     turn-around base                     =⟨ ! (app=-β turn-around base) ⟩
     ap (λ z → z base) (λ= turn-around)   =⟨ ! (loop-β (idf S¹) (λ= turn-around) |in-ctx (ap (λ z → z base))) ⟩
     ap (λ z → z base) (ap μ loop)        =⟨ ! (ap-∘ (λ z → z base) μ loop) ⟩
     ap (λ z → μ z base) loop             =⟨ ! (∙-unit-r _) ⟩
     ap (λ z → μ z base) loop ∙ idp ∎))
