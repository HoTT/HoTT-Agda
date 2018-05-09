{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.HSpace renaming (HSpaceStructure to HSS)
import homotopy.WedgeExtension as WedgeExt

module homotopy.Pi2HSuspCompose {i} {X : Ptd i} {{_ : has-level 1 (de⊙ X)}}
  {{is-0-connected : is-connected 0 (de⊙ X)}} (H-X : HSS X)
  (H-X-assoc : associator H-X)
  (coh-assoc-unit-l-r-pentagon : coh-unit-l-r-pentagon H-X H-X-assoc)
  where

  private
    A = de⊙ X
    e = pt X

  open import homotopy.Pi2HSusp H-X public

  infixr 80 _∙₁_
  _∙₁_ : {x y z : Susp A} → Trunc 1 (x == y) → Trunc 1 (y == z) → Trunc 1 (x == z)
  _∙₁_ {x} {y} {z} p q = _∙ₜ_ {A = Susp A} {ta = [ x ]} {tb = [ y ]} {tc = [ z ]} p q

  module _ {k} {B : Type k} where

    add-path-inverse-l : {x y z : B}
      → (p : y == x) (q : y == z)
      → q == (p ∙ ! p) ∙ q
    add-path-inverse-l p q = ap (λ s → s ∙ q) (! (!-inv-r p))

    add-path-inverse-r : {x y z : B}
      → (p : x == y) (q : y == z)
      → p == p ∙ (q ∙ ! q)
    add-path-inverse-r p q =
      ! (∙-unit-r p) ∙ ap (λ s → p ∙ s) (! (!-inv-r q))

    add-path-inverse-coh : {x y : B} (q : x == x) (p : x == y)
      → add-path-inverse-l p q
          ∙ ap (λ v → (p ∙ ! p) ∙ v) (add-path-inverse-r q p)
          ∙ ! (∙-assoc (p ∙ ! p) q (p ∙ ! p))
        == add-path-inverse-r q p
          ∙ ap (λ v → v ∙ p ∙ ! p) (add-path-inverse-l p q)
    add-path-inverse-coh q idp = ap (λ v → v ∙ idp) (ap-idf (add-path-inverse-r q idp))

  comp-l : (a' : A) → η (μ e a') == η a' ∙ η e
  comp-l a' = ap η (μ.unit-l a') ∙ add-path-inverse-r (η a') (merid e)

  comp-r : (a : A) → η (μ a e) == η e ∙ η a
  comp-r a = ap η (μ.unit-r a) ∙ add-path-inverse-l (merid e) (η a)

  comp-l₁ : (a' : A) → [ η (μ e a') ]₁ == [ η a' ∙ η e ]₁
  comp-l₁ = ap [_]₁ ∘ comp-l

  comp-r₁ : (a : A) → [ η (μ a e) ]₁ == [ η e ∙ η a ]₁
  comp-r₁ = ap [_]₁ ∘ comp-r

  comp-args : WedgeExt.args {i} {i} {A} {e} {A} {e}
  comp-args =
    record {
      m = -1; n = -1;
      P = λ a a' → (Q a a' , ⟨⟩);
      f = comp-r₁;
      g = comp-l₁;
      p = ap (λ {(p₁ , p₂) → ap [_] (ap η p₁ ∙ p₂)})
      (pair×= (! μ.coh) (coh (merid e)))
    }
    where
    Q : A → A → Type i
    Q a a' = [ η (μ a a' ) ]₁ == [ η a' ∙ η a ]₁
    coh : {B : Type i} {b b' : B} (p : b == b')
      → add-path-inverse-l p (p ∙ ! p) == add-path-inverse-r (p ∙ ! p) p
    coh idp = idp

  comp : (a a' : A) → [ η (μ a a') ]₁ == [ η a' ]₁ ∙₁ [ η a ]₁
  comp = WedgeExt.ext comp-args

  comp-unit-l : (a' : A) → comp e a' == comp-l₁ a'
  comp-unit-l a' = WedgeExt.β-r {r = comp-args} a'

  comp-unit-r : (a : A) → comp a e == comp-r₁ a
  comp-unit-r a = WedgeExt.β-l {r = comp-args} a

  module CoherenceProof (a' : A) where

    P : A → A → Type i
    P a a'' =
      comp (μ a a') a'' ∙ ap (λ v → [ η a'' ]₁ ∙₁ v) (comp a a') ∙ ap [_]₁ (! (∙-assoc (η a'') (η a') (η a)))
      == ap ([_]₁ ∘ η) (H-X-assoc a a' a'') ∙ comp a (μ a' a'') ∙ ap (λ v → v ∙₁ [ η a ]) (comp a' a'')

    P-is-prop : ∀ a a'' → is-prop (P a a'')
    P-is-prop a a'' = has-level-apply (has-level-apply (Trunc-level {n = 1}) _ _) _ _

    Q : A → A → hProp i
    Q a a'' = P a a'' , P-is-prop a a''

    inner-coh : comp-r (μ e a') ∙ ap (_∙_ (η e)) (comp-l a') ∙ ! (∙-assoc (η e) (η a') (η e))
                == ap η (H-X-assoc e a' e) ∙ comp-l (μ a' e) ∙ ap (λ v → v ∙ η e) (comp-r a')
    inner-coh =
      (comp-r (μ e a') ◃∙ ap (_∙_ (η e)) (comp-l a') ◃∙ ! (∙-assoc (η e) (η a') (η e)) ◃∎)
        =↯=⟨ 0 & 1 & (ap η (μ.unit-r (μ e a')) ◃∙ add-path-inverse-l (merid e) (η (μ e a')) ◃∎) & idp ⟩
      (ap η (μ.unit-r (μ e a'))
        ◃∙ add-path-inverse-l (merid e) (η (μ e a'))
        ◃∙ ap (_∙_ (η e)) (comp-l a')
        ◃∙ ! (∙-assoc (η e) (η a') (η e)) ◃∎)
        =↯=⟨ 2 & 1
            & (ap (_∙_ (η e)) (ap η (μ.unit-l a'))
              ◃∙ ap (_∙_ (η e)) (add-path-inverse-r (η a') (merid e)) ◃∎)
            & ap-∙ (_∙_ (η e)) (ap η (μ.unit-l a')) (add-path-inverse-r (η a') (merid e)) ⟩
      (ap η (μ.unit-r (μ e a'))
        ◃∙ add-path-inverse-l (merid e) (η (μ e a'))
        ◃∙ ap (_∙_ (η e)) (ap η (μ.unit-l a'))
        ◃∙ ap (_∙_ (η e)) (add-path-inverse-r (η a') (merid e))
        ◃∙ ! (∙-assoc (η e) (η a') (η e)) ◃∎)
        =↯=⟨ 1 & 2 & (ap η (μ.unit-l a') ◃∙ add-path-inverse-l (merid e) (η a') ◃∎)
            & ! (homotopy-naturality-from-idf (_∙_ (η e)) (add-path-inverse-l (merid e)) (ap η (μ.unit-l a'))) ⟩
      (ap η (μ.unit-r (μ e a'))
        ◃∙ ap η (μ.unit-l a')
        ◃∙ add-path-inverse-l (merid e) (η a')
        ◃∙ ap (_∙_ (η e)) (add-path-inverse-r (η a') (merid e))
        ◃∙ ! (∙-assoc (η e) (η a') (η e)) ◃∎)
        =↯=⟨ 2 & 3
            & (add-path-inverse-r (η a') (merid e)
              ◃∙ ap (λ v → v ∙ η e) (add-path-inverse-l (merid e) (η a')) ◃∎)
            & add-path-inverse-coh (η a') (merid e) ⟩
      (ap η (μ.unit-r (μ e a'))
        ◃∙ ap η (μ.unit-l a')
        ◃∙ add-path-inverse-r (η a') (merid e)
        ◃∙ ap (λ v → v ∙ η e) (add-path-inverse-l (merid e) (η a')) ◃∎)
        =↯=⟨ 0 & 2 & (ap η (H-X-assoc e a' e) ◃∙ ap η (μ.unit-l (μ a' e)) ◃∙ ap η (μ.unit-r a') ◃∎)
              & ap-seq-=↯= η (μ.unit-r (μ e a') ◃∙ μ.unit-l a' ◃∎)
                            (H-X-assoc e a' e ◃∙ μ.unit-l (μ a' e) ◃∙ μ.unit-r a' ◃∎)
                            (coh-assoc-unit-l-r-pentagon a') ⟩
      (ap η (H-X-assoc e a' e)
        ◃∙ ap η (μ.unit-l (μ a' e))
        ◃∙ ap η (μ.unit-r a')
        ◃∙ add-path-inverse-r (η a') (merid e)
        ◃∙ ap (λ v → v ∙ η e) (add-path-inverse-l (merid e) (η a')) ◃∎)
        =↯=⟨ 2 & 2
            & add-path-inverse-r (η (μ a' e)) (merid e) ◃∙ ap (λ v → v ∙ η e) (ap η (μ.unit-r a')) ◃∎
            & homotopy-naturality-from-idf (λ v → v ∙ η e)
                (λ v → add-path-inverse-r v (merid e))
                (ap η (μ.unit-r a')) ⟩
      (ap η (H-X-assoc e a' e)
        ◃∙ ap η (μ.unit-l (μ a' e))
        ◃∙ add-path-inverse-r (η (μ a' e)) (merid e)
        ◃∙ ap (λ v → v ∙ η e) (ap η (μ.unit-r a'))
        ◃∙ ap (λ v → v ∙ η e) (add-path-inverse-l (merid e) (η a')) ◃∎)
        =↯=⟨ 3 & 2 & ap (λ v → v ∙ η e) (comp-r a') ◃∎
            & ∙-ap (λ v → v ∙ η e) (ap η (μ.unit-r a')) (add-path-inverse-l (merid e) (η a')) ⟩
      (ap η (H-X-assoc e a' e)
        ◃∙ ap η (μ.unit-l (μ a' e))
        ◃∙ add-path-inverse-r (η (μ a' e)) (merid e)
        ◃∙ ap (λ v → v ∙ η e) (comp-r a') ◃∎)
        =↯=⟨ 1 & 2 & (comp-l (μ a' e) ◃∎) & idp ⟩
      (ap η (H-X-assoc e a' e) ◃∙ comp-l (μ a' e) ◃∙ ap (λ v → v ∙ η e) (comp-r a') ◃∎) ↯∎

    coh : P e e
    coh =
      (comp (μ e a') e ◃∙ ap (_∙₁_ [ η e ]₁) (comp e a') ◃∙ ap [_]₁ (! (∙-assoc (η e) (η a') (η e))) ◃∎)
        =↯=⟨ 0 & 1 & (comp-r₁ (μ e a') ◃∎) & comp-unit-r (μ e a') ⟩
      (comp-r₁ (μ e a') ◃∙ ap (_∙₁_ [ η e ]₁) (comp e a') ◃∙ ap [_]₁ (! (∙-assoc (η e) (η a') (η e))) ◃∎)
        =↯=⟨ 1 & 1 & (ap [_]₁ (ap (_∙_ (η e)) (comp-l a')) ◃∎) & step₂ ⟩
      (comp-r₁ (μ e a') ◃∙ ap [_]₁ (ap (_∙_ (η e)) (comp-l a')) ◃∙ ap [_]₁ (! (∙-assoc (η e) (η a') (η e))) ◃∎)
        ↯=⟨ ap-seq-=↯= [_]₁
              (comp-r (μ e a') ◃∙ ap (_∙_ (η e)) (comp-l a') ◃∙ ! (∙-assoc (η e) (η a') (η e)) ◃∎)
              (ap η (H-X-assoc e a' e) ◃∙ comp-l (μ a' e) ◃∙ ap (λ v → v ∙ η e) (comp-r a') ◃∎)
              inner-coh ⟩
      (ap [_]₁ (ap η (H-X-assoc e a' e)) ◃∙ comp-l₁ (μ a' e) ◃∙ ap [_]₁ (ap (λ v → v ∙ η e) (comp-r a')) ◃∎)
        =↯=⟨ 0 & 1 & (ap ([_]₁ ∘ η) (H-X-assoc e a' e) ◃∎) & ∘-ap [_]₁ η (H-X-assoc e a' e) ⟩
      (ap ([_]₁ ∘ η) (H-X-assoc e a' e) ◃∙ comp-l₁ (μ a' e) ◃∙ ap [_]₁ (ap (λ v → v ∙ η e) (comp-r a')) ◃∎)
        =↯=⟨ 1 & 1 & (comp e (μ a' e) ◃∎) & ! (comp-unit-l (μ a' e)) ⟩
      (ap ([_]₁ ∘ η) (H-X-assoc e a' e) ◃∙ comp e (μ a' e) ◃∙ ap [_]₁ (ap (λ v → v ∙ η e) (comp-r a')) ◃∎)
        =↯=⟨ 2 & 1 & (ap (λ v → v ∙₁ [ η e ]) (comp a' e) ◃∎) & step₈ ⟩
      (ap ([_]₁ ∘ η) (H-X-assoc e a' e) ◃∙ comp e (μ a' e) ◃∙ ap (λ v → v ∙₁ [ η e ]) (comp a' e) ◃∎) ↯∎
      where
      step₂ : ap (_∙₁_ [ η e ]₁) (comp e a') == ap [_]₁ (ap (_∙_ (η e)) (comp-l a'))
      step₂ =
        ap (_∙₁_ [ η e ]₁) (comp e a')
          =⟨ ap (ap (_∙₁_ [ η e ]₁)) (comp-unit-l a') ⟩
        ap (_∙₁_ [ η e ]₁) (comp-l₁ a')
          =⟨ ∘-ap (_∙₁_ [ η e ]₁) [_]₁ (comp-l a') ⟩
        ap ([_]₁ ∘ (_∙_ (η e))) (comp-l a')
          =⟨ ap-∘ [_]₁ (_∙_ (η e)) (comp-l a') ⟩
        ap [_]₁ (ap (_∙_ (η e)) (comp-l a')) ∎
      step₈ : ap [_]₁ (ap (λ v → v ∙ η e) (comp-r a')) == ap (λ v → v ∙₁ [ η e ]) (comp a' e)
      step₈ =
        ap [_]₁ (ap (λ v → v ∙ η e) (comp-r a'))
          =⟨ ∘-ap [_]₁ (λ v → v ∙ η e) (comp-r a') ⟩
        ap (λ v → [ v ∙ η e ]₁) (comp-r a')
          =⟨ ap-∘ (λ v → v ∙₁ [ η e ]₁) [_]₁ (comp-r a') ⟩
        ap (λ v → v ∙₁ [ η e ]₁) (comp-r₁ a')
          =⟨ ! (ap (ap (λ v → v ∙₁ [ η e ]₁)) (comp-unit-r a')) ⟩
        ap (λ v → v ∙₁ [ η e ]) (comp a' e) ∎

  comp-coh : (a a' a'' : A)
    →  comp (μ a a') a'' ∙ ap (λ v → [ η a'' ]₁ ∙₁ v) (comp a a') ∙ ap [_]₁ (! (∙-assoc (η a'') (η a') (η a)))
    == ap ([_]₁ ∘ η) (H-X-assoc a a' a'') ∙ comp a (μ a' a'') ∙ ap (λ v → v ∙₁ [ η a ]) (comp a' a'')
  comp-coh a a' a'' =
    prop-over-connected {A = A} {a = e} {{is-0-connected}}
                        (λ a → CoherenceProof.Q a' a a'')
                        (prop-over-connected {A = A} {a = e} {{is-0-connected}}
                                             (λ a'' → CoherenceProof.Q a' e a'')
                                             (CoherenceProof.coh a')
                                             a'')
                        a
