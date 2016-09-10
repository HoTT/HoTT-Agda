{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.HSpace

module homotopy.CircleHSpace where

⊙S¹-hSpace : HSpaceStructure ⊙S¹
⊙S¹-hSpace = hSpaceStructure μ μ-e-l μ-e-r μ-coh where

  turn-around : (x : S¹) → x == x
  turn-around = S¹-elim loop (↓-idf=idf-in (∙=∙' loop loop))

  module Mu = S¹Rec (idf S¹) (λ= turn-around)

  μ : S¹ → S¹ → S¹
  μ = Mu.f

  μ-e-l : (x : S¹) → μ base x == x
  μ-e-l x = idp

  μ-e-r : (x : S¹) → μ x base == x
  μ-e-r = S¹-elim idp (↓-app=idf-in
    (idp ∙' loop                          =⟨ ∙'-unit-l loop ⟩
     loop                                 =⟨ idp ⟩
     turn-around base                     =⟨ ! (app=-β turn-around base) ⟩
     ap (λ z → z base) (λ= turn-around)   =⟨ ! (Mu.loop-β |in-ctx (ap (λ z → z base))) ⟩
     ap (λ z → z base) (ap μ loop)        =⟨ ! (ap-∘ (λ z → z base) μ loop) ⟩
     ap (λ z → μ z base) loop             =⟨ ! (∙-unit-r _) ⟩
     ap (λ z → μ z base) loop ∙ idp ∎))

  μ-coh = idp
