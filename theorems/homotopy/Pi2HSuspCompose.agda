{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.HSpace renaming (HSpaceStructure to HSS)

module homotopy.Pi2HSuspCompose {i} {X : Ptd i} {{_ : has-level 1 (de⊙ X)}}
  {{is-0-connected : is-connected 0 (de⊙ X)}} (H-X : HSS X)
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

  -- comp' : {x y : Susp A} (p : north ==₁ x) (q : x ==₁ y) → μ (encode' p) (encode' q) == encode' (p ∙₁ q)
  -- comp' = {!!}

  module _ (H-space-assoc : ∀ a b c → μ (μ a b) c == μ a (μ b c))
           (H-space-assoc-coh : ∀ a b → μ.unit-r (μ a b) == H-space-assoc a b e ∙ ap (μ a) (μ.unit-r b)) where

    module InnerDiagram (y : A) where

      c₁ : north == south
      c₁ = merid (μ (μ e y) e)

      c₂ : north == south
      c₂ = merid e ∙ back ∙ merid (μ e y)

      c₃ : north == south
      c₃ = (merid e ∙ back) ∙ merid (μ e y)

      c₄ : north == south
      c₄ = (merid e ∙ back) ∙ merid y

      c₅ : north == south
      c₅ = (merid e ∙ back) ∙ merid y ∙ back ∙ merid e

      c₆ : north == south
      c₆ = merid (μ e (μ y e))

      c₇ : north == south
      c₇ = merid (μ y e)

      c₈ : north == south
      c₈ = merid (μ y e) ∙ back ∙ merid e

      c₉ : north == south
      c₉ = merid y ∙ back ∙ merid e

      c₁₀ : north == south
      c₁₀ = ((merid e ∙ back) ∙ merid y) ∙ back ∙ merid e

      c₁₁ : north == south
      c₁₁ = (merid e ∙ back ∙ merid y) ∙ back ∙ merid e

      c₁₂ : north == south
      c₁₂ = merid (μ e y)

      c₁₃ : north == south
      c₁₃ = merid y

      e₁₋₁₂ : c₁ == c₁₂
      e₁₋₁₂ = ap merid (μ.unit-r (μ e y))

      e₁₂₋₃ : c₁₂ == c₃
      e₁₂₋₃ = ap (λ s → s ∙ merid (μ e y)) (! (!-inv-r (merid e)))

      -- TODO: is this needed in this direction?
      e₃₋₁₂ : c₃ == c₁₂
      e₃₋₁₂ = ! e₁₂₋₃

      e₃₋₂ : c₃ == c₂
      e₃₋₂ = ∙-assoc (merid e) back (merid (μ e y))

      e₂₋₃ : c₂ == c₃
      e₂₋₃ = ! e₃₋₂

      e₁₋₂ : c₁ == c₂
      e₁₋₂ = e₁₋₁₂ ∙ e₁₂₋₃ ∙ e₃₋₂

      e₃₋₄ : c₃ == c₄
      e₃₋₄ = ap (λ v → (merid e ∙ back) ∙ v) $
             ap merid (μ.unit-l y)

      e₄₋₅ : c₄ == c₅
      e₄₋₅ = ap (λ v → (merid e ∙ back) ∙ v)
                (∙-add-path-and-inverse (merid y) (merid e))

      e₄₋₁₀ : c₄ == c₁₀
      e₄₋₁₀ = ∙-add-path-and-inverse ((merid e ∙ back) ∙ merid y) (merid e)

      e₃₋₅ : c₃ == c₅
      e₃₋₅ = e₃₋₄ ∙ e₄₋₅

      e₁₋₆ : c₁ == c₆
      e₁₋₆ = ap merid (H-space-assoc e y e)

      e₆₋₇ : c₆ == c₇
      e₆₋₇ = ap merid (μ.unit-l (μ y e))

      e₆₋₁₂ : c₆ == c₁₂
      e₆₋₁₂ = ap (λ s → merid (μ e s)) (μ.unit-r y)

      e₇₋₈ : c₇ == c₈
      e₇₋₈ = ∙-add-path-and-inverse (merid (μ y e)) (merid e)

      e₇₋₁₃ : c₇ == c₁₃
      e₇₋₁₃ = ap merid (μ.unit-r y)

      e₆₋₈ : c₆ == c₈
      e₆₋₈ = e₆₋₇ ∙ e₇₋₈

      e₈₋₉' : c₈ == c₉
      e₈₋₉' = ap (λ v → merid v ∙ back ∙ merid e) (μ.unit-r y)

      e₈₋₉ : c₈ == c₉
      e₈₋₉ = ap (λ v → v ∙ back ∙ merid e) $
             ap merid (μ.unit-r y)

      e₉₋₁₀ : c₉ == c₁₀
      e₉₋₁₀ = ap (λ v → v ∙ back ∙ merid e) $
              ap (λ w → w ∙ merid y) (! (!-inv-r (merid e)))

      e₁₀₋₁₁ : c₁₀ == c₁₁
      e₁₀₋₁₁ = ap (λ v → v ∙ back ∙ merid e) $
               ∙-assoc (merid e) back (merid y)

      e₁₁₋₁₀ : c₁₁ == c₁₀
      e₁₁₋₁₀ = ! e₁₀₋₁₁

      e₈₋₁₁ : c₈ == c₁₁
      e₈₋₁₁ = e₈₋₉ ∙ e₉₋₁₀ ∙ e₁₀₋₁₁

      e₁₀₋₅ : c₁₀ == c₅
      e₁₀₋₅ = ∙-assoc (merid e ∙ back) (merid y) (back ∙ merid e)

      e₁₂₋₁₃ : c₁₂ == c₁₃
      e₁₂₋₁₃ = ap merid (μ.unit-l y)

      e₁₃₋₄ : c₁₃ == c₄
      e₁₃₋₄ = ap (λ v → v ∙ merid y) (! (!-inv-r (merid e)))

      e₁₃₋₉ : c₁₃ == c₉
      e₁₃₋₉ = ∙-add-path-and-inverse (merid y) (merid e)

      cd₁ : e₃₋₂ ∙ e₂₋₃ == idp
      cd₁ = !-inv-r e₃₋₂

      cd₂ : e₁₂₋₃ ∙ e₃₋₄ == e₁₂₋₁₃ ∙ e₁₃₋₄
      cd₂ = ! (homotopy-naturality-from-idf (λ v → (merid e ∙ back) ∙ v)
                                            (λ v → ap (λ s → s ∙ v) (! (!-inv-r (merid e))))
                                            (ap merid (μ.unit-l y)))

      cd₃ : e₄₋₅ == e₄₋₁₀ ∙ e₁₀₋₅
      cd₃ = ∙-add-path-and-inverse-triangle (merid e ∙ back) (merid y) (merid e)
        where
        ∙-add-path-and-inverse-triangle : ∀ {k} {B : Type k} {w x y z : B}
          → (p : w == x) (p' : x == y) (q : z == y)
          → ap (λ s → p ∙ s) (∙-add-path-and-inverse p' q)
            == ∙-add-path-and-inverse (p ∙ p') q ∙ ∙-assoc p p' (! q ∙ q)
        ∙-add-path-and-inverse-triangle idp idp idp = idp

      cd₄ : e₁₃₋₄ ∙ e₄₋₁₀ == e₁₃₋₉ ∙ e₉₋₁₀
      cd₄ = homotopy-naturality-from-idf (λ v → v ∙ back ∙ merid e)
                                         (λ u → ∙-add-path-and-inverse u (merid e))
                                         (ap (λ s → s ∙ merid y) (! (!-inv-r (merid e))))

      cd₅ : e₁₋₁₂ == e₁₋₆ ∙ e₆₋₁₂
      cd₅ =
        e₁₋₁₂
          =⟨ ap (ap merid) (H-space-assoc-coh e y) ⟩
        ap merid (H-space-assoc e y e ∙ ap (μ e) (μ.unit-r y))
          =⟨ ap-∙ merid (H-space-assoc e y e) (ap (μ e) (μ.unit-r y)) ⟩
        e₁₋₆ ∙ ap merid (ap (μ e) (μ.unit-r y))
          =⟨ ap (λ v → e₁₋₆ ∙ v) (∘-ap merid (μ e) (μ.unit-r y)) ⟩
        e₁₋₆ ∙ e₆₋₁₂ ∎

      cd₆ : e₆₋₁₂ ∙ e₁₂₋₁₃ == e₆₋₇ ∙ e₇₋₁₃
      cd₆ = homotopy-naturality (merid ∘ μ e) merid (ap merid ∘ μ.unit-l) (μ.unit-r y)

      cd₇ : e₇₋₁₃ ∙ e₁₃₋₉ == e₇₋₈ ∙ e₈₋₉'
      cd₇ = homotopy-naturality merid (λ v → merid v ∙ back ∙ merid e) (λ v → ∙-add-path-and-inverse (merid v) (merid e)) (μ.unit-r y)

      cd₈ : e₈₋₉' == e₈₋₉
      cd₈ = ap-∘ (λ v → v ∙ back ∙ merid e) merid (μ.unit-r y)

      cd₉ : e₈₋₉ ∙ e₉₋₁₀ == e₈₋₁₁ ∙ e₁₁₋₁₀
      cd₉ =
        (e₈₋₉ ◃∙ e₉₋₁₀ ◃∎)
          ↯=⟨ 1 & 1 & (e₉₋₁₀ ◃∙ idp ◃∎) & (! (∙-unit-r e₉₋₁₀)) ⟩
        (e₈₋₉ ◃∙ e₉₋₁₀ ◃∙ idp ◃∎)
          ↯=⟨ 2 & 1 & (e₁₀₋₁₁ ◃∙ e₁₁₋₁₀ ◃∎) & (! (!-inv-r e₁₀₋₁₁)) ⟩
        (e₈₋₉ ◃∙ e₉₋₁₀ ◃∙ e₁₀₋₁₁ ◃∙ e₁₁₋₁₀ ◃∎)
          ↯=⟨ 0 & 3 & (e₈₋₁₁ ◃∎) & idp ⟩
        e₈₋₁₁ ∙ e₁₁₋₁₀ ∎

      cd : e₁₋₂ ∙ e₂₋₃ ∙ e₃₋₅ == e₁₋₆ ∙ e₆₋₈ ∙ e₈₋₁₁ ∙ e₁₁₋₁₀ ∙ e₁₀₋₅
      cd =
        (e₁₋₂ ◃∙ e₂₋₃ ◃∙ e₃₋₅ ◃∎)
          ↯=⟨ 0 & 1 & (e₁₋₁₂ ◃∙ e₁₂₋₃ ◃∙ e₃₋₂ ◃∎) & idp ⟩
        (e₁₋₁₂ ◃∙ e₁₂₋₃ ◃∙ e₃₋₂ ◃∙ e₂₋₃ ◃∙ e₃₋₅ ◃∎)
          ↯=⟨ 2 & 2 & (c₃ ∎∎) & cd₁ ⟩
        (e₁₋₁₂ ◃∙ e₁₂₋₃ ◃∙ e₃₋₅ ◃∎)
          ↯=⟨ 2 & 1 & (e₃₋₄ ◃∙ e₄₋₅ ◃∎) & idp ⟩
        (e₁₋₁₂ ◃∙ e₁₂₋₃ ◃∙ e₃₋₄ ◃∙ e₄₋₅ ◃∎)
          ↯=⟨ 1 & 2 & (e₁₂₋₁₃ ◃∙ e₁₃₋₄ ◃∎) & cd₂ ⟩
        (e₁₋₁₂ ◃∙ e₁₂₋₁₃ ◃∙ e₁₃₋₄ ◃∙ e₄₋₅ ◃∎)
          ↯=⟨ 3 & 1 & (e₄₋₁₀ ◃∙ e₁₀₋₅ ◃∎) & cd₃ ⟩
        (e₁₋₁₂ ◃∙ e₁₂₋₁₃ ◃∙ e₁₃₋₄ ◃∙ e₄₋₁₀ ◃∙ e₁₀₋₅ ◃∎)
          ↯=⟨ 2 & 2 & (e₁₃₋₉ ◃∙ e₉₋₁₀ ◃∎) & cd₄ ⟩
        (e₁₋₁₂ ◃∙ e₁₂₋₁₃ ◃∙ e₁₃₋₉ ◃∙ e₉₋₁₀ ◃∙ e₁₀₋₅ ◃∎)
          ↯=⟨ 0 & 1 & (e₁₋₆ ◃∙ e₆₋₁₂ ◃∎) & cd₅ ⟩
        (e₁₋₆ ◃∙ e₆₋₁₂ ◃∙ e₁₂₋₁₃ ◃∙ e₁₃₋₉ ◃∙ e₉₋₁₀ ◃∙ e₁₀₋₅ ◃∎)
          ↯=⟨ 1 & 2 & (e₆₋₇ ◃∙ e₇₋₁₃ ◃∎) & cd₆ ⟩
        (e₁₋₆ ◃∙ e₆₋₇ ◃∙ e₇₋₁₃ ◃∙ e₁₃₋₉ ◃∙ e₉₋₁₀ ◃∙ e₁₀₋₅ ◃∎)
          ↯=⟨ 2 & 2 & (e₇₋₈ ◃∙ e₈₋₉' ◃∎) & cd₇ ⟩
        (e₁₋₆ ◃∙ e₆₋₇ ◃∙ e₇₋₈ ◃∙ e₈₋₉' ◃∙ e₉₋₁₀ ◃∙ e₁₀₋₅ ◃∎)
          ↯=⟨ 3 & 1 & (e₈₋₉ ◃∎) & cd₈ ⟩
        (e₁₋₆ ◃∙ e₆₋₇ ◃∙ e₇₋₈ ◃∙ e₈₋₉ ◃∙ e₉₋₁₀ ◃∙ e₁₀₋₅ ◃∎)
          ↯=⟨ 1 & 2 & (e₆₋₈ ◃∎) & idp ⟩
        (e₁₋₆ ◃∙ e₆₋₈ ◃∙ e₈₋₉ ◃∙ e₉₋₁₀ ◃∙ e₁₀₋₅ ◃∎)
          ↯=⟨ 2 & 2 & (e₈₋₁₁ ◃∙ e₁₁₋₁₀ ◃∎) & cd₉ ⟩
        e₁₋₆ ∙ e₆₋₈ ∙ e₈₋₁₁ ∙ e₁₁₋₁₀ ∙ e₁₀₋₅ ∎

    {-
    module V1 (x y z : A) where

      ee : [ merid (μ (μ x y) z) ]₁ == [ (merid z ∙ back) ∙ merid y ∙ back ∙ merid x ]₁
      ee =
        [ merid (μ (μ x y) z) ]₁
          =⟨ homomorphism (μ x y) z ⟩
        [ merid z ∙ back ∙ merid (μ x y) ]₁
          =⟨ ap [_]₁ (! (∙-assoc (merid z) back (merid (μ x y)))) ⟩
        [ (merid z ∙ back) ∙ merid (μ x y) ]₁
          =⟨ ∙-∙₁ (merid z ∙ back) (merid (μ x y)) ⟩
        [ merid z ∙ back ]₁ ∙₁ [ merid (μ x y) ]₁
          =⟨ ap (λ s → [ merid z ∙ back ]₁ ∙₁ s) (homomorphism x y) ⟩
        [ merid z ∙ back ]₁ ∙₁ [ merid y ∙ back ∙ merid x ]₁
          =⟨ ! (∙-∙₁ (merid z ∙ back) (merid y ∙ back ∙ merid x)) ⟩
        [ (merid z ∙ back) ∙ merid y ∙ back ∙ merid x ]₁ =∎

    module V2 (x y z : A) where

      ee : [ merid (μ (μ x y) z) ]₁ == [ (merid z ∙ back) ∙ merid y ∙ back ∙ merid x ]₁
      ee =
        [ merid (μ (μ x y) z) ]₁
          =⟨ ap (λ s → [ merid s ]₁) (H-space-assoc x y z) ⟩
        [ merid (μ x (μ y z)) ]₁
          =⟨ homomorphism x (μ y z) ⟩
        [ merid (μ y z) ∙ back ∙ merid x ]₁
          =⟨ ∙-∙₁ (merid (μ y z)) (back ∙ merid x) ⟩
        [ merid (μ y z) ]₁ ∙₁ [ back ∙ merid x ]₁
          =⟨ ap (λ s → s ∙₁ [ back ∙ merid x ]) (homomorphism y z) ⟩
        [ merid z ∙ back ∙ merid y ]₁ ∙₁ [ back ∙ merid x ]₁
          =⟨ ! (∙-∙₁ (merid z ∙ back ∙ merid y) (back ∙ merid x)) ⟩
        [ (merid z ∙ back ∙ merid y) ∙ back ∙ merid x ]₁
          =⟨ ap (λ s → [ s ∙ back ∙ merid x ]₁) (! (∙-assoc (merid z) back (merid y))) ⟩
        [ ((merid z ∙ back) ∙ merid y) ∙ back ∙ merid x ]₁
          =⟨ ap [_]₁ (∙-assoc (merid z ∙ back) (merid y) (back ∙ merid x)) ⟩
        [ (merid z ∙ back) ∙ merid y ∙ back ∙ merid x ]₁ =∎

    homomorphism-coh : ∀ x y z → V1.ee x y z == V2.ee x y z
    homomorphism-coh =
      prop-over-connected {A = A} {a = e} {{is-0-connected}}
                          (λ x → (∀ y z → Q x y z) , Π-level (λ y → Π-level (Q-is-prop x y))) $
      prop-over-connected {A = A} {a = e} {{is-0-connected}}
                          (λ y → (∀ z → Q e y z) , Π-level (Q-is-prop e y)) $
      prop-over-connected {A = A} {a = e} {{is-0-connected}}
                          (λ z → Q e e z , Q-is-prop e e z) $
      {!!}
      where
      Q : A → A → A → Type i
      Q x y z = V1.ee x y z == V2.ee x y z
      Q-is-prop : ∀ x y z → is-prop (Q x y z)
      Q-is-prop x y z = has-level-apply (has-level-apply (Trunc-level {n = 1}) _ _) _ _
  -}

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
    [ (η y ∙ merid x) ∙ back ]₁
      =⟨ ap [_]₁ (∙-assoc (η y) (merid x) back) ⟩
    [ η y ∙ η x ]₁
      =⟨ ∙-∙₁ (η y) (η x) ⟩
    [ η y ]₁ ∙₁ [ η x ]₁ =∎
