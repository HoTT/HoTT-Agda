{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.HSpace

module homotopy.CircleHSpace where

⊙S¹-hSpace : HSpaceStructure ⊙S¹
⊙S¹-hSpace = hSpaceStructure ⊙μ ⊙unit-l ⊙unit-r where

  turn-around : (x : S¹) → x == x
  turn-around = S¹-elim loop (↓-idf=idf-in' (∙=∙' loop loop))

  module Mu = S¹Rec (idf S¹) (λ= turn-around)

  ⊙μ : (⊙S¹ ⊙× ⊙S¹) ⊙→ ⊙S¹
  ⊙μ = uncurry Mu.f , idp

  μ : S¹ → S¹ → S¹
  μ = Mu.f

  ⊙unit-l : ⊙μ ⊙∘ ⊙×-inr ⊙S¹ ⊙S¹ ⊙∼ ⊙idf ⊙S¹
  ⊙unit-l = (λ x → idp) , idp

  ⊙unit-r : ⊙μ ⊙∘ ⊙×-inl ⊙S¹ ⊙S¹ ⊙∼ ⊙idf ⊙S¹
  ⊙unit-r = (S¹-elim idp (↓-app=idf-in
    (idp ∙' loop                          =⟨ ∙'-unit-l loop ⟩
     loop                                 =⟨ idp ⟩
     turn-around base                     =⟨ ! (app=-β turn-around base) ⟩
     ap (λ z → z base) (λ= turn-around)   =⟨ ! (Mu.loop-β |in-ctx (ap (λ z → z base))) ⟩
     ap (λ z → z base) (ap μ loop)        =⟨ ∘-ap (λ z → z base) μ loop ⟩
     ap (λ z → μ z base) loop             =⟨ ! (∙-unit-r _) ⟩
     ap (λ z → μ z base) loop ∙ idp ∎)))
    , idp
