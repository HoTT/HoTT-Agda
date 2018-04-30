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

  infixr 80 _∙₁_
  _∙₁_ : {x y z : Susp A} → x ==₁ y → y ==₁ z → x ==₁ z
  _∙₁_ {x} {y} {z} p q = Trunc=-∙ {A = Susp A} {ta = [ x ]} {tb = [ y ]} {tc = [ z ]} p q

  -- TODO: generalize and move somewhere else
  ∙-∙₁ : {x y z : Susp A} (p : x == y) (q : y == z)
    → [ p ∙ q ]₁ == [ p ]₁ ∙₁ [ q ]₁
  ∙-∙₁ idp q = idp

  ∙₁-∙ : {x y z : Susp A} (p : x == y) (q : y == z)
    → [ p ]₁ ∙₁ [ q ]₁ == [ p ∙ q ]₁
  ∙₁-∙ p q = ! (∙-∙₁ p q)

  module _ (H-space-assoc : ∀ a b c → μ (μ a b) c == μ a (μ b c))
           (H-space-assoc-coh : ∀ a b → μ.unit-r (μ a b) == H-space-assoc a b e ∙ ap (μ a) (μ.unit-r b)) where

    module InnerDiagramObjects (x y z : A) where

      c₁ : north == south
      c₁ = merid (μ x (μ y z))

      c₂ : north == south
      c₂ = (merid (μ y z) ∙ back) ∙ merid x

      c₈ : north == south
      c₈ = ((merid z ∙ back) ∙ merid y ∙ back) ∙ merid x

      c₉ : north == south
      c₉ = (merid z ∙ back) ∙ (merid y ∙ back) ∙ merid x

      c₁₂ : north == south
      c₁₂ = (merid z ∙ back) ∙ merid (μ x y)

      c₁₃ : north == south
      c₁₃ = merid (μ (μ x y) z)

      c₁₄ : north == south
      c₁₄ = merid (μ x y)

      c₁₅ : north == south
      c₁₅ = (merid y ∙ back) ∙ merid x

      c₁₆ : north == south
      c₁₆ = (((merid z ∙ back) ∙ merid y) ∙ back) ∙ merid x

    module InnerDiagram (y : A) where

      open InnerDiagramObjects e y e

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
          =↯=⟨ 1 & 1 & (e₂₋₁₅ ◃∙ e₁₅₋₁₆ ◃∎) & cd₁ ⟩
        (e₁₋₂ ◃∙ e₂₋₁₅ ◃∙ e₁₅₋₁₆ ◃∙ e₁₆₋₈ ◃∎)
          =↯=⟨ 2 & 2 & (e₁₅₋₈ ◃∎) & cd₂ ⟩
        (e₁₋₂ ◃∙ e₂₋₁₅ ◃∙ e₁₅₋₈ ◃∎)
          =↯=⟨ 2 & 1 & (e₁₅₋₉ ◃∙ e₉₋₈ ◃∎) & cd₃ ⟩
        (e₁₋₂ ◃∙ e₂₋₁₅ ◃∙ e₁₅₋₉ ◃∙ e₉₋₈ ◃∎)
          =↯=⟨ 0 & 2 & (e₁₋₁₄ ◃∙ e₁₄₋₁₅ ◃∎) & cd₄ ⟩
        (e₁₋₁₄ ◃∙ e₁₄₋₁₅ ◃∙ e₁₅₋₉ ◃∙ e₉₋₈ ◃∎)
          =↯=⟨ 1 & 2 & (e₁₄₋₁₂ ◃∙ e₁₂₋₉ ◃∎) & cd₅ ⟩
        (e₁₋₁₄ ◃∙ e₁₄₋₁₂ ◃∙ e₁₂₋₉ ◃∙ e₉₋₈ ◃∎)
          =↯=⟨ 0 & 1 & (e₁₋₁₃ ◃∙ e₁₃₋₁₄ ◃∎) & cd₆ ⟩
        (e₁₋₁₃ ◃∙ e₁₃₋₁₄ ◃∙ e₁₄₋₁₂ ◃∙ e₁₂₋₉ ◃∙ e₉₋₈ ◃∎)
          =↯=⟨ 1 & 2 & (e₁₃₋₁₂ ◃∎) & idp ⟩
        e₁₋₁₃ ∙ e₁₃₋₁₂ ∙ e₁₂₋₉ ∙ e₉₋₈ ∎

    module IntermediateDiagramObjects (x y z : A) where

      module IDO = InnerDiagramObjects x y z

      c₁ : north ==₁ south
      c₁ = [ IDO.c₁ ]₁

      c₂ : north ==₁ south
      c₂ = [ IDO.c₂ ]₁

      c₃ : north ==₁ south
      c₃ = [ merid (μ y z) ∙ back ]₁ ∙₁ [ merid x ]₁

      c₄ : north ==₁ south
      c₄ = ([ merid (μ y z) ]₁ ∙₁ [ back ]₁) ∙₁ [ merid x ]₁

      c₅ : north ==₁ south
      c₅ = ([ (merid z ∙ back) ∙ merid y ]₁ ∙₁ [ back ]₁) ∙₁ [ merid x ]₁

      c₆ : north ==₁ south
      c₆ = [ ((merid z ∙ back) ∙ merid y) ∙ back ]₁ ∙₁ [ merid x ]₁

      c₇ : north ==₁ south
      c₇ = [ (merid z ∙ back) ∙ merid y ∙ back ]₁ ∙₁ [ merid x ]₁

      c₈ : north ==₁ south
      c₈ = [ IDO.c₈ ]₁

      c₉ : north ==₁ south
      c₉ = [ IDO.c₉ ]₁

      c₁₀ : north ==₁ south
      c₁₀ = [ merid z ∙ back ]₁ ∙₁ [ (merid y ∙ back) ∙ merid x ]₁

      c₁₁ : north ==₁ south
      c₁₁ = [ merid z ∙ back ]₁ ∙₁ [ merid (μ x y) ]₁

      c₁₂ : north ==₁ south
      c₁₂ = [ IDO.c₁₂ ]₁

      c₁₃ : north ==₁ south
      c₁₃ = [ IDO.c₁₃ ]₁

      c₁₆ : north ==₁ south
      c₁₆ = [ (((merid z ∙ back) ∙ merid y) ∙ back) ∙ merid x ]₁

    module IntermediateDiagramBorder (x y z : A) where

      open IntermediateDiagramObjects x y z

      e₁₋₂ : c₁ == c₂
      e₁₋₂ = homomorphism x (μ y z)

      e₁₋₁₃ : c₁ == c₁₃
      e₁₋₁₃ = ap (λ s → [ merid s ]₁) (! (H-space-assoc x y z))

      e₂₋₃ : c₂ == c₃
      e₂₋₃ = ∙-∙₁ (merid (μ y z) ∙ back) (merid x)

      e₃₋₄ : c₃ == c₄
      e₃₋₄ = ap (λ v → v ∙₁ [ merid x ]₁) (∙-∙₁ (merid (μ y z)) back)

      e₄₋₅ : c₄ == c₅
      e₄₋₅ = ap (λ v → (v ∙₁ [ back ]₁) ∙₁ [ merid x ]₁) (homomorphism y z)

      e₆₋₅ : c₆ == c₅
      e₆₋₅ = ap (λ v → v ∙₁ [ merid x ]₁) (∙-∙₁ ((merid z ∙ back) ∙ merid y) back)

      e₅₋₆ : c₅ == c₆
      e₅₋₆ = ! e₆₋₅

      e₆₋₇ : c₆ == c₇
      e₆₋₇ = ap (λ v → [ v ]₁ ∙₁ [ merid x ]₁) (∙-assoc (merid z ∙ back) (merid y) back)

      e₈₋₇ : c₈ == c₇
      e₈₋₇ = ∙-∙₁ ((merid z ∙ back) ∙ merid y ∙ back) (merid x)

      e₇₋₈ : c₇ == c₈
      e₇₋₈ = ! e₈₋₇

      e₉₋₈ : c₉ == c₈
      e₉₋₈ = ap [_]₁ (! (∙-assoc (merid z ∙ back) (merid y ∙ back) (merid x)))

      e₉₋₁₀ : c₉ == c₁₀
      e₉₋₁₀ = ∙-∙₁ (merid z ∙ back) ((merid y ∙ back) ∙ merid x)

      e₁₀₋₉ : c₁₀ == c₉
      e₁₀₋₉ = ! e₉₋₁₀

      e₁₁₋₁₀ : c₁₁ == c₁₀
      e₁₁₋₁₀ = ap (λ v → [ merid z ∙ back ]₁ ∙₁ v) (homomorphism x y)

      e₁₂₋₁₁ : c₁₂ == c₁₁
      e₁₂₋₁₁ = ∙-∙₁ (merid z ∙ back) (merid (μ x y))

      e₁₃₋₁₂ : c₁₃ == c₁₂
      e₁₃₋₁₂ = homomorphism (μ x y) z

      e₁₆₋₆ : c₁₆ == c₆
      e₁₆₋₆ = ∙-∙₁ (((merid z ∙ back) ∙ merid y) ∙ back) (merid x)

      e₁₆₋₈ : c₁₆ == c₈
      e₁₆₋₈ = ap (λ v → [ v ∙ merid x ]₁) (∙-assoc (merid z ∙ back) (merid y) back)

      e₁₋₈ : c₁ == c₈
      e₁₋₈ = e₁₋₂ ∙ e₂₋₃ ∙ e₃₋₄ ∙ e₄₋₅ ∙ e₅₋₆ ∙ e₆₋₇ ∙ e₇₋₈

      e₁₋₈' : c₁ == c₈
      e₁₋₈' = e₁₋₁₃ ∙ e₁₃₋₁₂ ∙ e₁₂₋₁₁ ∙ e₁₁₋₁₀ ∙ e₁₀₋₉ ∙ e₉₋₈

    module IntermediateDiagram (y : A) where

      private
        module ID = InnerDiagram y
      open IntermediateDiagramObjects e y e
      open IntermediateDiagramBorder e y e

      e₂₋₁₆ : c₂ == c₁₆
      e₂₋₁₆ = ap (λ v → [ (v ∙ back) ∙ merid e ]₁) (homomorphism-r y)

      e₃₋₆ : c₃ == c₆
      e₃₋₆ = ap (λ v → [ v ∙ back ]₁ ∙₁ [ merid e ]) (homomorphism-r y)

      e₄₋₅' : c₄ == c₅
      e₄₋₅' = ap (λ v → ([ v ]₁ ∙₁ [ back ]₁) ∙₁ [ merid e ]₁) (homomorphism-r y)

      e₁₁₋₁₀' : c₁₁ == c₁₀
      e₁₁₋₁₀' = ap (λ v → [ merid e ∙ back ]₁ ∙₁ [ v ]₁) (homomorphism-l y)

      e₁₂₋₉ : c₁₂ == c₉
      e₁₂₋₉ = ap (λ v → [ (merid e ∙ back) ∙ v ]₁) (homomorphism-l y)

      e₁₃₋₁₂' : c₁₃ == c₁₂
      e₁₃₋₁₂' = homomorphism-r₁ (μ e y)

      cd₁ : e₄₋₅ == e₄₋₅'
      cd₁ = step₁ ∙ step₂
        where
        e₄₋₅'' : c₄ == c₅
        e₄₋₅'' = ap (λ v → (v ∙₁ [ back ]₁) ∙₁ [ merid e ]₁) (homomorphism-r₁ y)
        step₁ : e₄₋₅ == e₄₋₅''
        step₁ = ap (ap (λ v → (v ∙₁ [ back ]₁) ∙₁ [ merid e ]₁)) (homomorphism-β-r y)
        step₂ : e₄₋₅'' == e₄₋₅'
        step₂ = ∘-ap (λ v → (v ∙₁ [ back ]₁) ∙₁ [ merid e ]₁) [_]₁ (homomorphism-r y)

      cd₂ : e₃₋₄ ∙ e₄₋₅' ∙ e₅₋₆ == e₃₋₆
      cd₂ = post-rearrange'-in (e₃₋₄ ◃∙ e₄₋₅' ◃∎) e₆₋₅ (e₃₋₆ ◃∎) $ ! $
            homotopy-naturality (λ v → [ v ∙ back ]₁ ∙₁ [ merid e ]₁)
                                (λ v → ([ v ]₁ ∙₁ [ back ]₁) ∙₁ [ merid e ]₁)
                                (λ v → ap (λ w → w ∙₁ [ merid e ]₁) (∙-∙₁ v back))
                                (homomorphism-r y)

      cd₃ : e₂₋₃ ∙ e₃₋₆ == e₂₋₁₆ ∙ e₁₆₋₆
      cd₃ = ! $
        homotopy-naturality (λ v → [ (v ∙ back) ∙ merid e ]₁)
                            (λ v → [ v ∙ back ]₁ ∙₁ [ merid e ]₁)
                            (λ v → ∙-∙₁ (v ∙ back) (merid e))
                            (homomorphism-r y)

      cd₄ : e₁₆₋₆ ∙ e₆₋₇ ∙ e₇₋₈ == e₁₆₋₈
      cd₄ = post-rearrange'-in (e₁₆₋₆ ◃∙ e₆₋₇ ◃∎) e₈₋₇ (e₁₆₋₈ ◃∎) $ ! $
            homotopy-naturality (λ v → [ v ∙ merid e ]₁)
                                (λ v → [ v ]₁ ∙₁ [ merid e ]₁)
                                (λ v → ∙-∙₁ v (merid e))
                                (∙-assoc (merid e ∙ back) (merid y) back)

      cd₅ : e₁₂₋₉ == e₁₂₋₁₁ ∙ e₁₁₋₁₀' ∙ e₁₀₋₉
      cd₅ = post-rearrange-in (e₁₂₋₉ ◃∎) (e₁₂₋₁₁ ◃∙ e₁₁₋₁₀' ◃∎) e₉₋₁₀ $
            homotopy-naturality (λ v → [ (merid e ∙ back) ∙ v ]₁)
                                (λ v → [ merid e ∙ back ]₁ ∙₁ [ v ]₁)
                                (λ v → ∙-∙₁ (merid e ∙ back) v)
                                (homomorphism-l y)

      cd₆ : e₁₁₋₁₀' == e₁₁₋₁₀
      cd₆ = step₁ ∙ step₂
        where
        e₁₁₋₁₀'' : c₁₁ == c₁₀
        e₁₁₋₁₀'' = ap (λ v → [ merid e ∙ back ]₁ ∙₁ v) (homomorphism-l₁ y)
        step₁ : e₁₁₋₁₀' == e₁₁₋₁₀''
        step₁ = ap-∘ (λ v → [ merid e ∙ back ]₁ ∙₁ v) [_]₁ (homomorphism-l y)
        step₂ : e₁₁₋₁₀'' == e₁₁₋₁₀
        step₂ = ! (ap (ap (λ v → [ merid e ∙ back ]₁ ∙₁ v)) (homomorphism-β-l y))

      cd : e₁₋₈ == e₁₋₈'
      cd =
        (e₁₋₂ ◃∙ e₂₋₃ ◃∙ e₃₋₄ ◃∙ e₄₋₅ ◃∙ e₅₋₆ ◃∙ e₆₋₇ ◃∙ e₇₋₈ ◃∎)
          =↯=⟨ 3 & 1 & (e₄₋₅' ◃∎) & cd₁ ⟩
        (e₁₋₂ ◃∙ e₂₋₃ ◃∙ e₃₋₄ ◃∙ e₄₋₅' ◃∙ e₅₋₆ ◃∙ e₆₋₇ ◃∙ e₇₋₈ ◃∎)
          =↯=⟨ 2 & 3 & (e₃₋₆ ◃∎) & cd₂ ⟩
        (e₁₋₂ ◃∙ e₂₋₃ ◃∙ e₃₋₆ ◃∙ e₆₋₇ ◃∙ e₇₋₈ ◃∎)
          =↯=⟨ 1 & 2 & (e₂₋₁₆ ◃∙ e₁₆₋₆ ◃∎) & cd₃ ⟩
        (e₁₋₂ ◃∙ e₂₋₁₆ ◃∙ e₁₆₋₆ ◃∙ e₆₋₇ ◃∙ e₇₋₈ ◃∎)
          =↯=⟨ 2 & 3 & (e₁₆₋₈ ◃∎) & cd₄ ⟩
        (e₁₋₂ ◃∙ e₂₋₁₆ ◃∙ e₁₆₋₈ ◃∎)
          =↯=⟨ 0 & 1 & (⟦ ID.e₁₋₂ ⟧₁ ◃∎) & homomorphism-β-l (μ y e) ⟩
        (⟦ ID.e₁₋₂ ⟧₁ ◃∙ e₂₋₁₆ ◃∙ e₁₆₋₈ ◃∎)
          =↯=⟨ 1 & 1 & (⟦ ID.e₂₋₁₆ ⟧₁ ◃∎) &
               ap-∘ [_]₁ (λ v → (v ∙ back) ∙ merid e) (homomorphism-r y) ⟩
        (⟦ ID.e₁₋₂ ⟧₁ ◃∙ ⟦ ID.e₂₋₁₆ ⟧₁ ◃∙ e₁₆₋₈ ◃∎)
          =↯=⟨ 2 & 1 & (⟦ ID.e₁₆₋₈ ⟧₁ ◃∎) & ap-∘ [_]₁ (λ v → v ∙ merid e) _ ⟩
        (⟦ ID.e₁₋₂ ⟧₁ ◃∙ ⟦ ID.e₂₋₁₆ ⟧₁ ◃∙ ⟦ ID.e₁₆₋₈ ⟧₁ ◃∎)
          ↯=⟨ ∙∙-ap [_]₁ ID.e₁₋₂ ID.e₂₋₁₆ ID.e₁₆₋₈ ⟩
        ⟦ ID.e₁₋₂ ∙ ID.e₂₋₁₆ ∙ ID.e₁₆₋₈ ⟧₁
          =⟨ ap ⟦_⟧₁ ID.cd ⟩
        ⟦ ID.e₁₋₁₃ ∙ ID.e₁₃₋₁₂ ∙ ID.e₁₂₋₉ ∙ ID.e₉₋₈ ⟧₁
          =⟨ ap-∙∙∙ [_]₁ ID.e₁₋₁₃ ID.e₁₃₋₁₂ ID.e₁₂₋₉ ID.e₉₋₈ ⟩
        (⟦ ID.e₁₋₁₃ ⟧₁ ◃∙ e₁₃₋₁₂' ◃∙ ⟦ ID.e₁₂₋₉ ⟧₁ ◃∙ e₉₋₈ ◃∎)
          =↯=⟨ 0 & 1 & (e₁₋₁₃ ◃∎) & ∘-ap [_]₁ merid _ ⟩
        (e₁₋₁₃ ◃∙ e₁₃₋₁₂' ◃∙ ⟦ ID.e₁₂₋₉ ⟧₁ ◃∙ e₉₋₈ ◃∎)
          =↯=⟨ 2 & 1 & (e₁₂₋₉ ◃∎) & ∘-ap [_]₁ (λ v → (merid e ∙ back) ∙ v) _ ⟩
        (e₁₋₁₃ ◃∙ e₁₃₋₁₂' ◃∙ e₁₂₋₉ ◃∙ e₉₋₈ ◃∎)
          =↯=⟨ 1 & 1 & (e₁₃₋₁₂ ◃∎) & ! (homomorphism-β-r (μ e y)) ⟩
        (e₁₋₁₃ ◃∙ e₁₃₋₁₂ ◃∙ e₁₂₋₉ ◃∙ e₉₋₈ ◃∎)
          =↯=⟨ 2 & 1 & (e₁₂₋₁₁ ◃∙ e₁₁₋₁₀' ◃∙ e₁₀₋₉ ◃∎) & cd₅ ⟩
        (e₁₋₁₃ ◃∙ e₁₃₋₁₂ ◃∙ e₁₂₋₁₁ ◃∙ e₁₁₋₁₀' ◃∙ e₁₀₋₉ ◃∙ e₉₋₈ ◃∎)
          =↯=⟨ 3 & 1 & (e₁₁₋₁₀ ◃∎) & cd₆ ⟩
        (e₁₋₁₃ ◃∙ e₁₃₋₁₂ ◃∙ e₁₂₋₁₁ ◃∙ e₁₁₋₁₀ ◃∙ e₁₀₋₉ ◃∙ e₉₋₈ ◃∎) ↯∎
        where
          ⟦_⟧₁ : ∀ {i} {B : Type i} {b b' : B} (p : b == b')
            → [ b ]₁ == [ b' ]₁
          ⟦_⟧₁ p = ap [_]₁ p

    homomorphism-coh' : ∀ y x z → IntermediateDiagramBorder.e₁₋₈ x y z
                                  == IntermediateDiagramBorder.e₁₋₈' x y z
    homomorphism-coh' y =
      prop-over-connected {A = A} {a = e} {{is-0-connected}}
                          (λ x → (∀ z → Q x z) , Π-level (Q-is-prop x)) $
      prop-over-connected {A = A} {a = e} {{is-0-connected}}
                          (λ z → Q e z , Q-is-prop e z) $
      IntermediateDiagram.cd y
      where
      Q : A → A → Type i
      Q x z = IntermediateDiagramBorder.e₁₋₈ x y z
              == IntermediateDiagramBorder.e₁₋₈' x y z
      Q-is-prop : ∀ x z → is-prop (Q x z)
      Q-is-prop x z = has-level-apply (has-level-apply (Trunc-level {n = 1}) _ _) _ _

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
