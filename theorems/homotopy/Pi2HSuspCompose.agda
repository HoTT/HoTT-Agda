{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.HSpace renaming (HSpaceStructure to HSS)

module homotopy.Pi2HSuspCompose {i} {X : Ptd i} {{_ : has-level 1 (de⊙ X)}}
  {{is-0-connected : is-connected 0 (de⊙ X)}} (H-X : HSS X)
  (H-X-assoc : associator H-X)
  (coh-assoc-unit-r : coh-unit-r H-X H-X-assoc)
  where

  open import homotopy.Pi2HSusp {i} {X} H-X
  open import homotopy.Pi2HSuspHomomorphismCoh {i} {X} H-X H-X-assoc coh-assoc-unit-r

  private
    A = de⊙ X
    e = pt X

  comp : (x y : A) → decodeN' (μ x y) == decodeN' y ∙₁ decodeN' x
  comp x y =
    [ η (μ x y) ]₁
      =⟨ ∙-∙₁ (merid (μ x y)) back ⟩
    [ merid (μ x y) ]₁ ∙₁ [ back ]₁
      =⟨ ap (λ z → z ∙₁ [ back ]₁) (homomorphism x y) ⟩
    [ η y ∙ merid x ]₁ ∙₁ [ back ]₁
      =⟨ ! (∙-∙₁ (η y ∙ merid x) back) ⟩
    [ (η y ∙ merid x) ∙ back ]₁
      =⟨ ap [_]₁ (∙-assoc (η y) (merid x) back) ⟩
    [ η y ∙ η x ]₁
      =⟨ ∙-∙₁ (η y) (η x) ⟩
    [ η y ]₁ ∙₁ [ η x ]₁ =∎
