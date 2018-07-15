{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.HSpace renaming (HSpaceStructure to HSS)
import homotopy.WedgeExtension as WedgeExt
open import lib.types.TwoSemiCategory
open import lib.two-semi-categories.FundamentalCategory

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
      → add-path-inverse-l p q ◃∙
        ap (λ v → (p ∙ ! p) ∙ v) (add-path-inverse-r q p) ◃∙
        ! (∙-assoc (p ∙ ! p) q (p ∙ ! p)) ◃∎
        =ₛ
        add-path-inverse-r q p ◃∙
        ap (λ v → v ∙ p ∙ ! p) (add-path-inverse-l p q) ◃∎
    add-path-inverse-coh q idp = =ₛ-in $
      ap (λ v → v ∙ idp) (ap-idf (add-path-inverse-r q idp))

  comp-l-seq : (a' : A) → η (μ e a') =-= η a' ∙ η e
  comp-l-seq a' =
    η (μ e a')
      =⟪ ap η (μ.unit-l a') ⟫
    η a'
      =⟪ add-path-inverse-r (η a') (merid e) ⟫
    η a' ∙ η e ∎∎

  comp-l : (a' : A) → η (μ e a') == η a' ∙ η e
  comp-l a' = ↯ (comp-l-seq a')

  comp-r-seq : (a : A) → η (μ a e) =-= η e ∙ η a
  comp-r-seq a =
    η (μ a e)
      =⟪ ap η (μ.unit-r a) ⟫
    η a
      =⟪ add-path-inverse-l (merid e) (η a) ⟫
    η e ∙ η a ∎∎

  comp-r : (a : A) → η (μ a e) == η e ∙ η a
  comp-r a = ↯ (comp-r-seq a)

  comp-lr-coh : comp-r e == comp-l e
  comp-lr-coh =
    ap2 (λ p₁ p₂ → ap η p₁ ∙ p₂)
        (! μ.coh)
        (add-path-inverse-lr-coh (merid e))
    where
    add-path-inverse-lr-coh : {B : Type i} {b b' : B} (p : b == b')
      → add-path-inverse-l p (p ∙ ! p) == add-path-inverse-r (p ∙ ! p) p
    add-path-inverse-lr-coh idp = idp

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
      p = ap (ap [_]₁) comp-lr-coh
    }
    where
    Q : A → A → Type i
    Q a a' = [ η (μ a a' ) ]₁ == [ η a' ∙ η a ]₁

  comp : (a a' : A) → [ η (μ a a') ]₁ == [ η a' ]₁ ∙₁ [ η a ]₁
  comp = WedgeExt.ext comp-args

  comp-unit-l : (a' : A) → comp e a' == comp-l₁ a'
  comp-unit-l a' = WedgeExt.β-r {r = comp-args} a'

  comp-unit-r : (a : A) → comp a e == comp-r₁ a
  comp-unit-r a = WedgeExt.β-l {r = comp-args} a

  module CoherenceProof (a' : A) where

    P : A → A → Type i
    P a a'' =
      comp (μ a a') a'' ◃∙
      ap ([ η a'' ]₁ ∙₁_) (comp a a') ◃∙
      ! (ap [_]₁ (∙-assoc (η a'') (η a') (η a))) ◃∎
      =ₛ
      ap ([_]₁ ∘ η) (H-X-assoc a a' a'') ◃∙
      comp a (μ a' a'') ◃∙
      ap (_∙₁ [ η a ]₁) (comp a' a'') ◃∎

    P-is-prop : ∀ a a'' → is-prop (P a a'')
    P-is-prop a a'' = =ₛ-level (Trunc-level {n = 1})

    Q  : A → A → hProp i
    Q a a'' = P a a'' , P-is-prop a a''

    inner-coh :
      comp-r (μ e a') ◃∙
      ap (_∙_ (η e)) (comp-l a') ◃∙
      ! (∙-assoc (η e) (η a') (η e)) ◃∎
      =ₛ
      ap η (H-X-assoc e a' e) ◃∙
      comp-l (μ a' e) ◃∙
      ap (λ v → v ∙ η e) (comp-r a') ◃∎
    inner-coh =
      comp-r (μ e a') ◃∙
      ap (η e ∙_) (comp-l a') ◃∙
      ! (∙-assoc (η e) (η a') (η e)) ◃∎
        =ₛ⟨ 0 & 1 & expand (ap η (μ.unit-r (μ e a')) ◃∙
                            add-path-inverse-l (merid e) (η (μ e a')) ◃∎) ⟩
      ap η (μ.unit-r (μ e a')) ◃∙
      add-path-inverse-l (merid e) (η (μ e a')) ◃∙
      ap (η e ∙_) (comp-l a') ◃∙
      ! (∙-assoc (η e) (η a') (η e)) ◃∎
        =ₛ⟨ 2 & 1 & ap-seq-∙ (_∙_ (η e)) (comp-l-seq a') ⟩
      ap η (μ.unit-r (μ e a')) ◃∙
      add-path-inverse-l (merid e) (η (μ e a')) ◃∙
      ap (η e ∙_) (ap η (μ.unit-l a')) ◃∙
      ap (η e ∙_) (add-path-inverse-r (η a') (merid e)) ◃∙
      ! (∙-assoc (η e) (η a') (η e)) ◃∎
        =ₛ⟨ 1 & 2 & !ₛ $
            homotopy-naturality-from-idf (_∙_ (η e))
                                         (add-path-inverse-l (merid e))
                                         (ap η (μ.unit-l a')) ⟩
      ap η (μ.unit-r (μ e a')) ◃∙
      ap η (μ.unit-l a') ◃∙
      add-path-inverse-l (merid e) (η a') ◃∙
      ap (η e ∙_) (add-path-inverse-r (η a') (merid e)) ◃∙
      ! (∙-assoc (η e) (η a') (η e)) ◃∎
        =ₛ⟨ 2 & 3 & add-path-inverse-coh (η a') (merid e) ⟩
      ap η (μ.unit-r (μ e a')) ◃∙
      ap η (μ.unit-l a') ◃∙
      add-path-inverse-r (η a') (merid e) ◃∙
      ap (_∙ η e) (add-path-inverse-l (merid e) (η a')) ◃∎
        =ₛ⟨ 0 & 2 & ap-seq-=ₛ η (coh-assoc-unit-l-r-pentagon a') ⟩
      ap η (H-X-assoc e a' e) ◃∙
      ap η (μ.unit-l (μ a' e)) ◃∙
      ap η (μ.unit-r a') ◃∙
      add-path-inverse-r (η a') (merid e) ◃∙
      ap (_∙ η e) (add-path-inverse-l (merid e) (η a')) ◃∎
        =ₛ⟨ 2 & 2 &
            homotopy-naturality-from-idf (_∙ η e)
                                         (λ v → add-path-inverse-r v (merid e))
                                         (ap η (μ.unit-r a')) ⟩
      ap η (H-X-assoc e a' e) ◃∙
      ap η (μ.unit-l (μ a' e)) ◃∙
      add-path-inverse-r (η (μ a' e)) (merid e) ◃∙
      ap (_∙ η e) (ap η (μ.unit-r a')) ◃∙
      ap (_∙ η e) (add-path-inverse-l (merid e) (η a')) ◃∎
        =ₛ⟨ 3 & 2 & ∙-ap-seq (_∙ η e) (comp-r-seq a')⟩
      ap η (H-X-assoc e a' e) ◃∙
      ap η (μ.unit-l (μ a' e)) ◃∙
      add-path-inverse-r (η (μ a' e)) (merid e) ◃∙
      ap (_∙ η e) (comp-r a') ◃∎
        =ₛ₁⟨ 1 & 2 & idp ⟩
      ap η (H-X-assoc e a' e) ◃∙
      comp-l (μ a' e) ◃∙
      ap (_∙ η e) (comp-r a') ◃∎ ∎ₛ

    coh : P e e
    coh =
      comp (μ e a') e ◃∙
      ap (_∙₁_ [ η e ]₁) (comp e a') ◃∙
      ! (ap [_]₁ (∙-assoc (η e) (η a') (η e))) ◃∎
        =ₛ₁⟨ 2 & 1 & !-ap [_]₁ (∙-assoc (η e) (η a') (η e)) ⟩
      comp (μ e a') e ◃∙
      ap (_∙₁_ [ η e ]₁) (comp e a') ◃∙
      ap [_]₁ (! (∙-assoc (η e) (η a') (η e))) ◃∎
        =ₛ₁⟨ 0 & 1 & comp-unit-r (μ e a') ⟩
      comp-r₁ (μ e a') ◃∙
      ap (_∙₁_ [ η e ]₁) (comp e a') ◃∙
      ap [_]₁ (! (∙-assoc (η e) (η a') (η e))) ◃∎
        =ₛ₁⟨ 1 & 1 & step₂ ⟩
      comp-r₁ (μ e a') ◃∙
      ap [_]₁ (ap (_∙_ (η e)) (comp-l a')) ◃∙
      ap [_]₁ (! (∙-assoc (η e) (η a') (η e))) ◃∎
        =ₛ⟨ 0 & 3 & ap-seq-=ₛ [_]₁ inner-coh ⟩
      ap [_]₁ (ap η (H-X-assoc e a' e)) ◃∙
      comp-l₁ (μ a' e) ◃∙
      ap [_]₁ (ap (λ v → v ∙ η e) (comp-r a')) ◃∎
        =ₛ₁⟨ 0 & 1 & ∘-ap [_]₁ η (H-X-assoc e a' e) ⟩
      ap ([_]₁ ∘ η) (H-X-assoc e a' e) ◃∙
      comp-l₁ (μ a' e) ◃∙
      ap [_]₁ (ap (λ v → v ∙ η e) (comp-r a')) ◃∎
        =ₛ₁⟨ 1 & 1 & ! (comp-unit-l (μ a' e)) ⟩
      ap ([_]₁ ∘ η) (H-X-assoc e a' e) ◃∙
      comp e (μ a' e) ◃∙
      ap [_]₁ (ap (λ v → v ∙ η e) (comp-r a')) ◃∎
        =ₛ₁⟨ 2 & 1 & step₈ ⟩
      ap ([_]₁ ∘ η) (H-X-assoc e a' e) ◃∙
      comp e (μ a' e) ◃∙
      ap (λ v → v ∙₁ [ η e ]) (comp a' e) ◃∎ ∎ₛ
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
      step₈ : ap [_]₁ (ap (λ v → v ∙ η e) (comp-r a')) == ap (_∙₁ [ η e ]) (comp a' e)
      step₈ =
        ap [_]₁ (ap (_∙ η e) (comp-r a'))
          =⟨ ∘-ap [_]₁ (_∙ η e) (comp-r a') ⟩
        ap (λ v → [ v ∙ η e ]₁) (comp-r a')
          =⟨ ap-∘ (_∙₁ [ η e ]₁) [_]₁ (comp-r a') ⟩
        ap (_∙₁ [ η e ]₁) (comp-r₁ a')
          =⟨ ! (ap (ap (_∙₁ [ η e ]₁)) (comp-unit-r a')) ⟩
        ap (_∙₁ [ η e ]) (comp a' e) ∎

  abstract
    comp-coh : (a a' a'' : A)
      → comp (μ a a') a'' ◃∙
        ap (λ v → [ η a'' ]₁ ∙₁ v) (comp a a') ◃∙
        ! (ap [_]₁ (∙-assoc (η a'') (η a') (η a))) ◃∎
        =ₛ
        ap ([_]₁ ∘ η) (H-X-assoc a a' a'') ◃∙
        comp a (μ a' a'') ◃∙
        ap (λ v → v ∙₁ [ η a ]) (comp a' a'') ◃∎
    comp-coh a a' a'' =
      prop-over-connected {A = A} {a = e} {{is-0-connected}}
                          (λ a → CoherenceProof.Q a' a a'')
                          (prop-over-connected {A = A} {a = e} {{is-0-connected}}
                                              (λ a'' → CoherenceProof.Q a' e a'')
                                              (CoherenceProof.coh a')
                                              a'')
                          a

  comp-functor : (pentagon : coh-assoc-pentagon H-X H-X-assoc)
    → TwoSemiFunctor
        (HSpace-2-semi-category H-X {{⟨⟩}} H-X-assoc pentagon)
        (dual-cat (=ₜ-fundamental-cat (Susp (de⊙ X))))
  comp-functor _ =
    record
    { F₀ = λ _ → [ north ]
    ; F₁ = λ x → [ η x ]
    ; pres-comp = comp
    ; pres-comp-coh = comp-coh
    }
