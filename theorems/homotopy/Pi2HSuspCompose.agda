{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.HSpace renaming (HSpaceStructure to HSS)

module homotopy.Pi2HSuspCompose {i} {X : Ptd i} {{_ : has-level 1 (de⊙ X)}}
  {{_ : is-connected 0 (de⊙ X)}} (H-X : HSS X)
  where

  open import homotopy.Pi2HSusp {i} {X} H-X

  private
    A = de⊙ X
    e = pt X

  _==₁_ : (x y : Susp A) → Type i
  _==₁_ x y = Trunc 1 (x == y)

  [_]₁ : {x y : Susp A} → x == y → x ==₁ y
  [_]₁ p = [ p ]

  infixr 80 _∙₁_
  _∙₁_ : {x y z : Susp A} → x ==₁ y → y ==₁ z → x ==₁ z
  _∙₁_ {x} {y} {z} p q = Trunc=-∙ {A = Susp A} {ta = [ x ]} {tb = [ y ]} {tc = [ z ]} p q

  -- TODO: generalize and move somewhere else
  ∙-∙₁ : {x y z : Susp A} (p : x == y) (q : y == z)
    → [ p ∙ q ]₁ == [ p ]₁ ∙₁ [ q ]₁
  ∙-∙₁ idp q = idp

  back : south == north
  back = ! (merid e)

  comp : (x y : A) → decodeN' (μ x y) == decodeN' y ∙₁ decodeN' x
  comp x y =
    [ η (μ x y) ]₁
      =⟨ ∙-∙₁ (merid (μ x y)) back ⟩
    [ merid (μ x y) ]₁ ∙₁ [ back ]₁
      =⟨ ap (λ z → z ∙₁ [ back ]₁) (homomorphism x y) ⟩
    [ merid y ∙ back ∙ merid x ]₁ ∙₁ [ back ]₁
      =⟨ ! (∙-∙₁ (merid y ∙ back ∙ merid x) back) ⟩
    [ (merid y ∙ back ∙ merid x) ∙ back ]₁
      =⟨ ! (ap (λ z → [ z ∙ back ]₁) (∙-assoc (merid y) back (merid x))) ⟩
    [ ((merid y ∙ back) ∙ merid x) ∙ back ]₁
      =⟨ ap [_]₁ (∙-assoc (merid y ∙ back) (merid x) back) ⟩
    [ η y ∙ η x ]₁
      =⟨ ∙-∙₁ (η y) (η x) ⟩
    [ η y ]₁ ∙₁ [ η x ]₁ =∎
