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

  module _ (H-space-assoc : ∀ a b c → μ (μ a b) c == μ a (μ b c))
           (H-space-assoc-coh : ∀ a b → μ.unit-r (μ a b) == H-space-assoc a b e ∙ ap (μ a) (μ.unit-r b)) where

    module InnerDiagram (y : A) where

      c₁ : north == south
      c₁ = merid (μ e (μ y e))

      c₂ : north == south
      c₂ = (merid (μ y e) ∙ back) ∙ merid e

      c₈ : north == south
      c₈ = ((merid e ∙ back) ∙ merid y ∙ back) ∙ merid e

      c₉ : north == south
      c₉ = (merid e ∙ back) ∙ (merid y ∙ back) ∙ merid e

      c₁₂ : north == south
      c₁₂ = (merid e ∙ back) ∙ merid (μ e y)

      c₁₃ : north == south
      c₁₃ = merid (μ (μ e y) e)

      c₁₄ : north == south
      c₁₄ = merid (μ e y)

      c₁₅ : north == south
      c₁₅ = (merid y ∙ back) ∙ merid e

      c₁₆ : north == south
      c₁₆ = (((merid e ∙ back) ∙ merid y) ∙ back) ∙ merid e

      e₁₋₂ : c₁ == c₂
      e₁₋₂ = homomorphism-l (μ y e)

      e₁₋₁₃ : c₁ == c₁₃
      e₁₋₁₃ = ap merid (! (H-space-assoc e y e))

      e₁₋₁₄ : c₁ == c₁₄
      e₁₋₁₄ = ap merid (ap (μ e) (μ.unit-r y))

      e₂₋₁₅ : c₂ == c₁₅
      e₂₋₁₅ = ap (λ v → (v ∙ back) ∙ merid e) $
              ap merid (μ.unit-r y)

      e₂₋₁₆ : c₂ == c₁₆
      e₂₋₁₆ = ap (λ v → (v ∙ back) ∙ merid e) (homomorphism-r y)

      e₁₂₋₉ : c₁₂ == c₉
      e₁₂₋₉ = ap (λ v → (merid e ∙ back) ∙ v) (homomorphism-l y)

      e₉₋₈ : c₉ == c₈
      e₉₋₈ = ! (∙-assoc (merid e ∙ back) (merid y ∙ back) (merid e))

      e₁₃₋₁₄ : c₁₃ == c₁₄
      e₁₃₋₁₄ = ap merid (μ.unit-r (μ e y))

      e₁₄₋₁₂ : c₁₄ == c₁₂
      e₁₄₋₁₂ = add-path-and-inverse-l (merid e) (merid (μ e y))

      e₁₃₋₁₂ : c₁₃ == c₁₂
      e₁₃₋₁₂ = e₁₃₋₁₄ ∙ e₁₄₋₁₂

      e₁₄₋₁₅ : c₁₄ == c₁₅
      e₁₄₋₁₅ = homomorphism-l y

      e₁₅₋₁₆ : c₁₅ == c₁₆
      e₁₅₋₁₆ = ap (λ v → (v ∙ back) ∙ merid e) $
               add-path-and-inverse-l (merid e) (merid y)

      e₁₅₋₈ : c₁₅ == c₈
      e₁₅₋₈ = ap (λ v → v ∙ merid e) $
              add-path-and-inverse-l (merid e) (merid y ∙ back)

      e₁₅₋₉ : c₁₅ == c₉
      e₁₅₋₉ = add-path-and-inverse-l (merid e) ((merid y ∙ back) ∙ merid e)

      e₁₆₋₈ : c₁₆ == c₈
      e₁₆₋₈ = ap (λ v → v ∙ merid e) (∙-assoc (merid e ∙ back) (merid y) back)

      cd₁ : e₂₋₁₆ == e₂₋₁₅ ∙ e₁₅₋₁₆
      cd₁ = ap-∙ (λ v → (v ∙ back) ∙ merid e)
                 (ap merid (μ.unit-r y))
                 (add-path-and-inverse-l (merid e) (merid y))

      add-path-and-inverse-l-triangle : ∀ {k} {B : Type k} {w x y z : B}
        (p : x == w) (q : x == y) (q' : y == z)
        → ap (λ s → s ∙ q') (add-path-and-inverse-l p q) ∙ ∙-assoc (p ∙ ! p) q q'
          == add-path-and-inverse-l p (q ∙ q')
      add-path-and-inverse-l-triangle idp idp idp = idp

      cd₂ : e₁₅₋₁₆ ∙ e₁₆₋₈ == e₁₅₋₈
      cd₂ =
        e₁₅₋₁₆ ∙ e₁₆₋₈
          =⟨ ap (λ s → s ∙ e₁₆₋₈) step₁ ⟩
        e₁₅₋₁₆' ∙ e₁₆₋₈
          =⟨ step₂ ⟩
        e₁₅₋₈'
          =⟨ step₃ ⟩
        e₁₅₋₈ ∎
        where
          e₁₅₋₁₆' : c₁₅ == c₁₆
          e₁₅₋₁₆' = ap (λ w → w ∙ merid e) $
                    ap (λ v → v ∙ back) $
                    add-path-and-inverse-l (merid e) (merid y)
          e₁₅₋₈' : c₁₅ == c₈
          e₁₅₋₈' = ap (λ w → w ∙ merid e) $
                   (ap (λ v → v ∙ back) $ add-path-and-inverse-l (merid e) (merid y)) ∙
                   (∙-assoc (merid e ∙ back) (merid y) back)
          step₁ : e₁₅₋₁₆ == e₁₅₋₁₆'
          step₁ = ap-∘ (λ w → w ∙ merid e)
                       (λ v → v ∙ back)
                       (add-path-and-inverse-l (merid e) (merid y))
          step₂ : e₁₅₋₁₆' ∙ e₁₆₋₈ == e₁₅₋₈'
          step₂ = ∙-ap (λ w → w ∙ merid e)
                       (ap (λ v → v ∙ back) $ add-path-and-inverse-l (merid e) (merid y))
                       (∙-assoc (merid e ∙ back) (merid y) back)
          step₃ : e₁₅₋₈' == e₁₅₋₈
          step₃ = ap (ap (λ w → w ∙ merid e)) $
                  add-path-and-inverse-l-triangle (merid e) (merid y) back

      cd₃ : e₁₅₋₈ == e₁₅₋₉ ∙ e₉₋₈
      cd₃ = post-rearrange-in (e₁₅₋₈ ◃∎) (e₁₅₋₉ ◃∎) e₈₋₉ $
            add-path-and-inverse-l-triangle (merid e) (merid y ∙ back) (merid e)
        where
        e₈₋₉ : c₈ == c₉
        e₈₋₉ = ∙-assoc (merid e ∙ back) (merid y ∙ back) (merid e)

      cd₄ : e₁₋₂ ∙ e₂₋₁₅ == e₁₋₁₄ ∙ e₁₄₋₁₅
      cd₄ =
        e₁₋₂ ∙ e₂₋₁₅
          =⟨ ap (λ v → e₁₋₂ ∙ v) step₁ ⟩
        e₁₋₂ ∙ e₂₋₁₅'
          =⟨ step₂ ⟩
        e₁₋₁₄' ∙ e₁₄₋₁₅
          =⟨ ap (λ v → v ∙ e₁₄₋₁₅) step₃ ⟩
        e₁₋₁₄ ∙ e₁₄₋₁₅ ∎
        where
          e₂₋₁₅' : c₂ == c₁₅
          e₂₋₁₅' = ap (λ x → (merid x ∙ back) ∙ merid e) (μ.unit-r y)
          e₁₋₁₄' : c₁ == c₁₄
          e₁₋₁₄' = ap (λ x → merid (μ e x)) (μ.unit-r y)
          step₁ : e₂₋₁₅ == e₂₋₁₅'
          step₁ = ∘-ap (λ v → (v ∙ back) ∙ merid e) merid (μ.unit-r y)
          step₂ : e₁₋₂ ∙ e₂₋₁₅' == e₁₋₁₄' ∙ e₁₄₋₁₅
          step₂ = ! $
            homotopy-naturality (λ x → merid (μ e x))
                                (λ x → (merid x ∙ back) ∙ merid e)
                                homomorphism-l
                                (μ.unit-r y)
          step₃ : e₁₋₁₄' == e₁₋₁₄
          step₃ = ap-∘ merid (μ e) (μ.unit-r y)

      cd₅ : e₁₄₋₁₅ ∙ e₁₅₋₉ == e₁₄₋₁₂ ∙ e₁₂₋₉
      cd₅ = homotopy-naturality-from-idf (λ v → (merid e ∙ back) ∙ v)
                                         (add-path-and-inverse-l (merid e))
                                         (homomorphism-l y)

      cd₆ : e₁₋₁₄ == e₁₋₁₃ ∙ e₁₃₋₁₄
      cd₆ =
        e₁₋₁₄
          =⟨ step₁ ⟩
        e₁₋₁₄'
          =⟨ step₂ ⟩
        e₁₋₁₃ ∙ e₁₃₋₁₄ ∎
        where
          e₁₋₁₄' : c₁ == c₁₄
          e₁₋₁₄' = ap merid $
                   ! (H-space-assoc e y e) ∙ μ.unit-r (μ e y)
          step₁ : e₁₋₁₄ == e₁₋₁₄'
          step₁ = ap (ap merid) step₁'
            where
            step₁' : ap (μ e) (μ.unit-r y) == ! (H-space-assoc e y e) ∙ μ.unit-r (μ e y)
            step₁' = pre-rotate-in (ap (μ e) (μ.unit-r y)) (H-space-assoc e y e) (μ.unit-r (μ e y)) $
                     ! (H-space-assoc-coh e y)
          step₂ : e₁₋₁₄' == e₁₋₁₃ ∙ e₁₃₋₁₄
          step₂ = ap-∙ merid (! (H-space-assoc e y e)) (μ.unit-r (μ e y))

      cd : e₁₋₂ ∙ e₂₋₁₆ ∙ e₁₆₋₈ == e₁₋₁₃ ∙ e₁₃₋₁₂ ∙ e₁₂₋₉ ∙ e₉₋₈
      cd =
        (e₁₋₂ ◃∙ e₂₋₁₆ ◃∙ e₁₆₋₈ ◃∎)
          ↯=⟨ 1 & 1 & (e₂₋₁₅ ◃∙ e₁₅₋₁₆ ◃∎) & cd₁ ⟩
        (e₁₋₂ ◃∙ e₂₋₁₅ ◃∙ e₁₅₋₁₆ ◃∙ e₁₆₋₈ ◃∎)
          ↯=⟨ 2 & 2 & (e₁₅₋₈ ◃∎) & cd₂ ⟩
        (e₁₋₂ ◃∙ e₂₋₁₅ ◃∙ e₁₅₋₈ ◃∎)
          ↯=⟨ 2 & 1 & (e₁₅₋₉ ◃∙ e₉₋₈ ◃∎) & cd₃ ⟩
        (e₁₋₂ ◃∙ e₂₋₁₅ ◃∙ e₁₅₋₉ ◃∙ e₉₋₈ ◃∎)
          ↯=⟨ 0 & 2 & (e₁₋₁₄ ◃∙ e₁₄₋₁₅ ◃∎) & cd₄ ⟩
        (e₁₋₁₄ ◃∙ e₁₄₋₁₅ ◃∙ e₁₅₋₉ ◃∙ e₉₋₈ ◃∎)
          ↯=⟨ 1 & 2 & (e₁₄₋₁₂ ◃∙ e₁₂₋₉ ◃∎) & cd₅ ⟩
        (e₁₋₁₄ ◃∙ e₁₄₋₁₂ ◃∙ e₁₂₋₉ ◃∙ e₉₋₈ ◃∎)
          ↯=⟨ 0 & 1 & (e₁₋₁₃ ◃∙ e₁₃₋₁₄ ◃∎) & cd₆ ⟩
        (e₁₋₁₃ ◃∙ e₁₃₋₁₄ ◃∙ e₁₄₋₁₂ ◃∙ e₁₂₋₉ ◃∙ e₉₋₈ ◃∎)
          ↯=⟨ 1 & 2 & (e₁₃₋₁₂ ◃∎) & idp ⟩
        e₁₋₁₃ ∙ e₁₃₋₁₂ ∙ e₁₂₋₉ ∙ e₉₋₈ ∎

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

  {-
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
  -}
