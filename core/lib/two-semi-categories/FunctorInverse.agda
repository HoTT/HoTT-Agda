{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.PathSeq
open import lib.types.Paths
open import lib.types.TwoSemiCategory
open import lib.two-semi-categories.Functor

module lib.two-semi-categories.FunctorInverse where

module _ {k l} {B : Type k} {C : B → B → Type l}
  (comp : {b b' b'' : B} → C b b' → C b' b'' → C b b'') where

  coe-C : {b₁ b₁' b₂ b₂' : B}
    → b₁ == b₂
    → b₁' == b₂'
    → C b₁ b₁'
    → C b₂ b₂'
  coe-C p p' = coe (ap2 C p p')

  coe-comp : {b₁ b₁' b₁'' b₂ b₂' b₂'' : B}
    → (p : b₁ == b₂) (p' : b₁' == b₂') (p'' : b₁'' == b₂'')
    → (r : C b₁ b₁') (s : C b₁' b₁'')
    → coe-C p p'' (comp r s) == comp (coe-C p p' r) (coe-C p' p'' s)
  coe-comp idp idp idp r s = idp

  coe-comp-coh : {b₁ b₁' b₁'' b₁''' b₂ b₂' b₂'' b₂''' : B}
    → (assoc : {b b' b'' b''' : B}
             → (f : C b b') (g : C b' b'') (h : C b'' b''')
             → comp (comp f g) h == comp f (comp g h))
    → (p : b₁ == b₂) (p' : b₁' == b₂') (p'' : b₁'' == b₂'') (p''' : b₁''' == b₂''')
    → (f : C b₁ b₁') (g : C b₁' b₁'') (h : C b₁'' b₁''')
    → coe-comp p p'' p''' (comp f g) h ∙ ap (λ s → comp s (coe-C p'' p''' h)) (coe-comp p p' p'' f g) ∙ assoc (coe-C p p' f) (coe-C p' p'' g) (coe-C p'' p''' h)
      == ap (coe-C p p''') (assoc f g h) ∙ coe-comp p p' p''' f (comp g h) ∙ ap (comp (coe-C p p' f)) (coe-comp p' p'' p''' g h)
  coe-comp-coh assoc idp idp idp idp f g h =
    ! (ap-idf (assoc f g h)) ∙ ! (∙-unit-r (ap (coe-C idp idp) (assoc f g h)))

functor-inverse : ∀ {i₁ j₁ i₂ j₂}
  {C : TwoSemiCategory i₁ j₁} {D : TwoSemiCategory i₂ j₂}
  → (F : TwoSemiFunctor C D)
  → is-equiv (TwoSemiFunctor.F₀ F)
  → ((x y : TwoSemiCategory.El C) → is-equiv (TwoSemiFunctor.F₁ F {x} {y}))
  → TwoSemiFunctor D C
functor-inverse {C = C} {D = D} F F₀-equiv F₁-equiv =
  record
  { F₀ = F₀
  ; F₁ = F₁
  ; pres-comp = pres-comp
  ; pres-comp-coh = pres-comp-coh
  }
  where
    module C = TwoSemiCategory C
    module D = TwoSemiCategory D
    module F = TwoSemiFunctor F
    F₀ : D.El → C.El
    F₀ = is-equiv.g F₀-equiv
    F₁' : {x y : D.El} → D.Arr (F.F₀ (F₀ x)) (F.F₀ (F₀ y)) → C.Arr (F₀ x) (F₀ y)
    F₁' {x} {y} f = is-equiv.g (F₁-equiv (F₀ x) (F₀ y)) f
    F₁'-f-g : {x y : D.El} → (f : D.Arr (F.F₀ (F₀ x)) (F.F₀ (F₀ y)))
      → F.F₁ (F₁' f) == f
    F₁'-f-g {x} {y} f = is-equiv.f-g (F₁-equiv (F₀ x) (F₀ y)) f
    F₁'-f-g! : {x y : D.El} → (f : D.Arr (F.F₀ (F₀ x)) (F.F₀ (F₀ y)))
      → f == F.F₁ (F₁' f)
    F₁'-f-g! f = ! (F₁'-f-g f)
    F₁'-g-f : {x y : D.El} → (f : C.Arr (F₀ x) (F₀ y))
      → F₁' (F.F₁ f) == f
    F₁'-g-f {x} {y} f = is-equiv.g-f (F₁-equiv (F₀ x) (F₀ y)) f
    F₀-f-g : (x : D.El) → x == F.F₀ (F₀ x)
    F₀-f-g x = ! (is-equiv.f-g F₀-equiv x)
    Arr-equiv : (x y : D.El) → D.Arr x y == D.Arr (F.F₀ (F₀ x)) (F.F₀ (F₀ y))
    Arr-equiv x y = ap2 D.Arr (F₀-f-g x) (F₀-f-g y)
    F₁'' : {x y : D.El} → D.Arr x y → D.Arr (F.F₀ (F₀ x)) (F.F₀ (F₀ y))
    F₁'' {x} {y} f = coe (Arr-equiv x y) f
    F₁ : {x y : D.El} → D.Arr x y → C.Arr (F₀ x) (F₀ y)
    F₁ f = F₁' (F₁'' f)
    F₁''-pres-comp : {x y z : D.El} (f : D.Arr x y) (g : D.Arr y z)
      → F₁'' (D.comp f g) == D.comp (F₁'' f) (F₁'' g)
    F₁''-pres-comp {x} {y} {z} f g =
      coe-comp D.comp (F₀-f-g x) (F₀-f-g y) (F₀-f-g z) f g
    F₁'-pres-comp-↯ : {x y z : D.El}
      (f : D.Arr (F.F₀ (F₀ x)) (F.F₀ (F₀ y)))
      (g : D.Arr (F.F₀ (F₀ y)) (F.F₀ (F₀ z)))
      → F₁' (D.comp f g) =-= C.comp (F₁' f) (F₁' g)
    F₁'-pres-comp-↯ {x} {y} {z} f g =
      F₁' (D.comp f g)
        =⟪ ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! g) ⟫
      F₁' (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g)))
        =⟪ ap F₁' (! (F.pres-comp (F₁' f) (F₁' g))) ⟫
      F₁' (F.F₁ (C.comp (F₁' f) (F₁' g)))
        =⟪ F₁'-g-f (C.comp (F₁' f) (F₁' g)) ⟫
      C.comp (F₁' f) (F₁' g) ∎∎
    F₁'-pres-comp : {x y z : D.El}
      (f : D.Arr (F.F₀ (F₀ x)) (F.F₀ (F₀ y)))
      (g : D.Arr (F.F₀ (F₀ y)) (F.F₀ (F₀ z)))
      → F₁' (D.comp f g) == C.comp (F₁' f) (F₁' g)
    F₁'-pres-comp f g = ↯ F₁'-pres-comp-↯ f g
    pres-comp-↯ : {x y z : D.El} (f : D.Arr x y) (g : D.Arr y z)
      → F₁ (D.comp f g) =-= C.comp (F₁ f) (F₁ g)
    pres-comp-↯ {x} {y} {z} f g =
      F₁' (F₁'' (D.comp f g))
        =⟪ ap F₁' (F₁''-pres-comp f g) ⟫
      F₁' (D.comp (F₁'' f) (F₁'' g))
        =⟪ F₁'-pres-comp (F₁'' f) (F₁'' g) ⟫
      C.comp (F₁ f) (F₁ g) ∎∎
    pres-comp : {x y z : D.El} (f : D.Arr x y) (g : D.Arr y z)
      → F₁ (D.comp f g) == C.comp (F₁ f) (F₁ g)
    pres-comp f g = ↯ pres-comp-↯ f g
    F₁''-pres-comp-coh : {w x y z : D.El}
      (f : D.Arr w x) (g : D.Arr x y) (h : D.Arr y z)
      → F₁''-pres-comp (D.comp f g) h ∙ ap (λ s → D.comp s (F₁'' h)) (F₁''-pres-comp f g) ∙ D.assoc (F₁'' f) (F₁'' g) (F₁'' h)
        == ap F₁'' (D.assoc f g h) ∙ F₁''-pres-comp f (D.comp g h) ∙ ap (D.comp (F₁'' f)) (F₁''-pres-comp g h)
    F₁'-pres-comp-coh : {w x y z : D.El}
      (f : D.Arr (F.F₀ (F₀ w)) (F.F₀ (F₀ x)))
      (g : D.Arr (F.F₀ (F₀ x)) (F.F₀ (F₀ y)))
      (h : D.Arr (F.F₀ (F₀ y)) (F.F₀ (F₀ z)))
      → F₁'-pres-comp (D.comp f g) h ∙ ap (λ s → C.comp s (F₁' h)) (F₁'-pres-comp f g) ∙ C.assoc (F₁' f) (F₁' g) (F₁' h)
        == ap F₁' (D.assoc f g h) ∙ F₁'-pres-comp f (D.comp g h) ∙ ap (C.comp (F₁' f)) (F₁'-pres-comp g h)
    F₁'-pres-comp-coh {w} {x} {y} {z} f g h =
      (F₁'-pres-comp (D.comp f g) h
      ◃∙ ap (λ s → C.comp s (F₁' h)) (F₁'-pres-comp f g)
      ◃∙ C.assoc (F₁' f) (F₁' g) (F₁' h) ◃∎)
        =↯=⟨ 0 & 1 & F₁'-pres-comp-↯ (D.comp f g) h & idp ⟩
      (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! (D.comp f g)) (F₁'-f-g! h)
      ◃∙ ap F₁' (! (F.pres-comp (F₁' (D.comp f g)) (F₁' h)))
      ◃∙ F₁'-g-f (C.comp (F₁' (D.comp f g)) (F₁' h))
      ◃∙ ap (λ s → C.comp s (F₁' h)) (F₁'-pres-comp f g)
      ◃∙ C.assoc (F₁' f) (F₁' g) (F₁' h) ◃∎)
        =↯=⟨ 2 & 2 & !ₛ $
             homotopy-naturality-=ₛ
               (λ s → F₁' (F.F₁ (C.comp s (F₁' h))))
               (λ s → C.comp s (F₁' h))
               (λ s → F₁'-g-f (C.comp s (F₁' h)))
               (F₁'-pres-comp f g) ⟩
      (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! (D.comp f g)) (F₁'-f-g! h)
      ◃∙ ap F₁' (! (F.pres-comp (F₁' (D.comp f g)) (F₁' h)))
      ◃∙ ap (λ s → F₁' (F.F₁ (C.comp s (F₁' h)))) (F₁'-pres-comp f g)
      ◃∙ F₁'-g-f (C.comp (C.comp (F₁' f) (F₁' g)) (F₁' h))
      ◃∙ C.assoc (F₁' f) (F₁' g) (F₁' h) ◃∎)
        =↯=⟨ 1 & 2 & !ₛ $
             homotopy-naturality-=ₛ
               (λ s → F₁' (D.comp (F.F₁ s) (F.F₁ (F₁' h))))
               (λ s → F₁' (F.F₁ (C.comp s (F₁' h))))
               (λ s → ap F₁' (! (F.pres-comp s (F₁' h))))
               (F₁'-pres-comp f g) ⟩
      (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! (D.comp f g)) (F₁'-f-g! h)
      ◃∙ ap (λ s → F₁' (D.comp (F.F₁ s) (F.F₁ (F₁' h)))) (F₁'-pres-comp f g)
      ◃∙ ap F₁' (! (F.pres-comp (C.comp (F₁' f) (F₁' g)) (F₁' h)))
      ◃∙ F₁'-g-f (C.comp (C.comp (F₁' f) (F₁' g)) (F₁' h))
      ◃∙ C.assoc (F₁' f) (F₁' g) (F₁' h) ◃∎)
        =↯=⟨ 1 & 1 & ap-seq (λ s → F₁' (D.comp (F.F₁ s) (F.F₁ (F₁' h)))) (F₁'-pres-comp-↯ f g)
               & ap-seq-∙ (λ s → F₁' (D.comp (F.F₁ s) (F.F₁ (F₁' h)))) (F₁'-pres-comp-↯ f g) ⟩
      (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! (D.comp f g)) (F₁'-f-g! h)
      ◃∙ ap (λ s → F₁' (D.comp (F.F₁ s) (F.F₁ (F₁' h)))) (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! g))
      ◃∙ ap (λ s → F₁' (D.comp (F.F₁ s) (F.F₁ (F₁' h)))) (ap F₁' (! (F.pres-comp (F₁' f) (F₁' g))))
      ◃∙ ap (λ s → F₁' (D.comp (F.F₁ s) (F.F₁ (F₁' h)))) (F₁'-g-f (C.comp (F₁' f) (F₁' g)))
      ◃∙ ap F₁' (! (F.pres-comp (C.comp (F₁' f) (F₁' g)) (F₁' h)))
      ◃∙ F₁'-g-f (C.comp (C.comp (F₁' f) (F₁' g)) (F₁' h))
      ◃∙ C.assoc (F₁' f) (F₁' g) (F₁' h) ◃∎)
        =↯=⟨ 3 & 1 & step₅ ⟩
      (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! (D.comp f g)) (F₁'-f-g! h)
      ◃∙ ap (λ s → F₁' (D.comp (F.F₁ s) (F.F₁ (F₁' h)))) (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! g))
      ◃∙ ap (λ s → F₁' (D.comp (F.F₁ s) (F.F₁ (F₁' h)))) (ap F₁' (! (F.pres-comp (F₁' f) (F₁' g))))
      ◃∙ ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) (F₁'-f-g (F.F₁ (C.comp (F₁' f) (F₁' g))))
      ◃∙ ap F₁' (! (F.pres-comp (C.comp (F₁' f) (F₁' g)) (F₁' h)))
      ◃∙ F₁'-g-f (C.comp (C.comp (F₁' f) (F₁' g)) (F₁' h))
      ◃∙ C.assoc (F₁' f) (F₁' g) (F₁' h) ◃∎)
        =↯=⟨ 2 & 1 & (ap (λ s → F₁' (D.comp (F.F₁ (F₁' s)) (F.F₁ (F₁' h)))) (! (F.pres-comp (F₁' f) (F₁' g))) ◃∎)
               & ∘-ap (λ s → F₁' (D.comp (F.F₁ s) (F.F₁ (F₁' h))))
                      F₁' (! (F.pres-comp (F₁' f) (F₁' g))) ⟩
      (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! (D.comp f g)) (F₁'-f-g! h)
      ◃∙ ap (λ s → F₁' (D.comp (F.F₁ s) (F.F₁ (F₁' h)))) (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! g))
      ◃∙ ap (λ s → F₁' (D.comp (F.F₁ (F₁' s)) (F.F₁ (F₁' h)))) (! (F.pres-comp (F₁' f) (F₁' g)))
      ◃∙ ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) (F₁'-f-g (F.F₁ (C.comp (F₁' f) (F₁' g))))
      ◃∙ ap F₁' (! (F.pres-comp (C.comp (F₁' f) (F₁' g)) (F₁' h)))
      ◃∙ F₁'-g-f (C.comp (C.comp (F₁' f) (F₁' g)) (F₁' h))
      ◃∙ C.assoc (F₁' f) (F₁' g) (F₁' h) ◃∎)
        =↯=⟨ 2 & 2 &
             homotopy-naturality-=ₛ
               (λ s → F₁' (D.comp (F.F₁ (F₁' s)) (F.F₁ (F₁' h))))
               (λ s → F₁' (D.comp s (F.F₁ (F₁' h))))
               (λ t → ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) (F₁'-f-g t))
               (! (F.pres-comp (F₁' f) (F₁' g))) ⟩
      (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! (D.comp f g)) (F₁'-f-g! h)
      ◃∙ ap (λ s → F₁' (D.comp (F.F₁ s) (F.F₁ (F₁' h)))) (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! g))
      ◃∙ ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) (F₁'-f-g (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g))))
      ◃∙ ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) (! (F.pres-comp (F₁' f) (F₁' g)))
      ◃∙ ap F₁' (! (F.pres-comp (C.comp (F₁' f) (F₁' g)) (F₁' h)))
      ◃∙ F₁'-g-f (C.comp (C.comp (F₁' f) (F₁' g)) (F₁' h))
      ◃∙ C.assoc (F₁' f) (F₁' g) (F₁' h) ◃∎)
        =↯=⟨ 0 & 3 & step₈ ⟩
      (ap (λ s → F₁' (D.comp (D.comp s g) h)) (F₁'-f-g! f)
      ◃∙ ap (λ s → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) s) h)) (F₁'-f-g! g)
      ◃∙ ap (λ s → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g))) s)) (F₁'-f-g! h)
      ◃∙ ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) (! (F.pres-comp (F₁' f) (F₁' g)))
      ◃∙ ap F₁' (! (F.pres-comp (C.comp (F₁' f) (F₁' g)) (F₁' h)))
      ◃∙ F₁'-g-f (C.comp (C.comp (F₁' f) (F₁' g)) (F₁' h))
      ◃∙ C.assoc (F₁' f) (F₁' g) (F₁' h) ◃∎)
        =↯=⟨ 5 & 2 & !ₛ $
             homotopy-naturality-to-idf-=ₛ (F₁' ∘ F.F₁) F₁'-g-f (C.assoc (F₁' f) (F₁' g) (F₁' h)) ⟩
      (ap (λ s → F₁' (D.comp (D.comp s g) h)) (F₁'-f-g! f)
      ◃∙ ap (λ s → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) s) h)) (F₁'-f-g! g)
      ◃∙ ap (λ s → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g))) s)) (F₁'-f-g! h)
      ◃∙ ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) (! (F.pres-comp (F₁' f) (F₁' g)))
      ◃∙ ap F₁' (! (F.pres-comp (C.comp (F₁' f) (F₁' g)) (F₁' h)))
      ◃∙ ap (F₁' ∘ F.F₁) (C.assoc (F₁' f) (F₁' g) (F₁' h))
      ◃∙ F₁'-g-f (C.comp (F₁' f) (C.comp (F₁' g) (F₁' h))) ◃∎)
        =↯=⟨ 3 & 3 & step₁₀ ⟩
      (ap (λ s → F₁' (D.comp (D.comp s g) h)) (F₁'-f-g! f)
      ◃∙ ap (λ s → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) s) h)) (F₁'-f-g! g)
      ◃∙ ap (λ s → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g))) s)) (F₁'-f-g! h)
      ◃∙ ap F₁' (D.assoc (F.F₁ (F₁' f)) (F.F₁ (F₁' g)) (F.F₁ (F₁' h)))
      ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (! (F.pres-comp (F₁' g) (F₁' h)))
      ◃∙ ap F₁' (! (F.pres-comp (F₁' f) (C.comp (F₁' g) (F₁' h))))
      ◃∙ F₁'-g-f (C.comp (F₁' f) (C.comp (F₁' g) (F₁' h))) ◃∎)
        =↯=⟨ 0 & 4 & step₁₁ ⟩
      (ap F₁' (D.assoc f g h)
      ◃∙ ap (λ s → F₁' (D.comp s (D.comp g h))) (F₁'-f-g! f)
      ◃∙ ap (λ s → F₁' (D.comp (F.F₁ (F₁' f)) (D.comp s h))) (F₁'-f-g! g)
      ◃∙ ap (λ s → F₁' (D.comp (F.F₁ (F₁' f)) (D.comp (F.F₁ (F₁' g)) s))) (F₁'-f-g! h)
      ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (! (F.pres-comp (F₁' g) (F₁' h)))
      ◃∙ ap F₁' (! (F.pres-comp (F₁' f) (C.comp (F₁' g) (F₁' h))))
      ◃∙ F₁'-g-f (C.comp (F₁' f) (C.comp (F₁' g) (F₁' h))) ◃∎)
        =↯=⟨ 1 & 3 & step₁₂ ⟩
      (ap F₁' (D.assoc f g h)
      ◃∙ ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! (D.comp g h))
      ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁) (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! g) (F₁'-f-g! h))
      ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (F₁'-f-g (D.comp (F.F₁ (F₁' g)) (F.F₁ (F₁' h))))
      ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (! (F.pres-comp (F₁' g) (F₁' h)))
      ◃∙ ap F₁' (! (F.pres-comp (F₁' f) (C.comp (F₁' g) (F₁' h))))
      ◃∙ F₁'-g-f (C.comp (F₁' f) (C.comp (F₁' g) (F₁' h))) ◃∎)
        =↯=⟨ 3 & 2 & !ₛ $
             homotopy-naturality-=ₛ
               (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁ ∘ F₁')
               (F₁' ∘ D.comp (F.F₁ (F₁' f)))
               (ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) ∘ F₁'-f-g)
               (! (F.pres-comp (F₁' g) (F₁' h))) ⟩
      (ap F₁' (D.assoc f g h)
      ◃∙ ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! (D.comp g h))
      ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁) (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! g) (F₁'-f-g! h))
      ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁ ∘ F₁') (! (F.pres-comp (F₁' g) (F₁' h)))
      ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (F₁'-f-g (F.F₁ (C.comp (F₁' g) (F₁' h))))
      ◃∙ ap F₁' (! (F.pres-comp (F₁' f) (C.comp (F₁' g) (F₁' h))))
      ◃∙ F₁'-g-f (C.comp (F₁' f) (C.comp (F₁' g) (F₁' h))) ◃∎)
        =↯=⟨ 3 & 1 & ap (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁) (ap F₁' (! (F.pres-comp (F₁' g) (F₁' h)))) ◃∎
               & ap-∘ (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁) F₁' (! (F.pres-comp (F₁' g) (F₁' h))) ⟩
      (ap F₁' (D.assoc f g h)
      ◃∙ ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! (D.comp g h))
      ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁) (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! g) (F₁'-f-g! h))
      ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁) (ap F₁' (! (F.pres-comp (F₁' g) (F₁' h))))
      ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (F₁'-f-g (F.F₁ (C.comp (F₁' g) (F₁' h))))
      ◃∙ ap F₁' (! (F.pres-comp (F₁' f) (C.comp (F₁' g) (F₁' h))))
      ◃∙ F₁'-g-f (C.comp (F₁' f) (C.comp (F₁' g) (F₁' h))) ◃∎)
        =↯=⟨ 4 & 1 & ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (ap F.F₁ (F₁'-g-f (C.comp (F₁' g) (F₁' h)))) ◃∎
          & ap (ap (F₁' ∘ D.comp (F.F₁ (F₁' f))))
               (! (is-equiv.adj (F₁-equiv (F₀ x) (F₀ z)) (C.comp (F₁' g) (F₁' h)))) ⟩
      (ap F₁' (D.assoc f g h)
      ◃∙ ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! (D.comp g h))
      ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁) (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! g) (F₁'-f-g! h))
      ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁) (ap F₁' (! (F.pres-comp (F₁' g) (F₁' h))))
      ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (ap F.F₁ (F₁'-g-f (C.comp (F₁' g) (F₁' h))))
      ◃∙ ap F₁' (! (F.pres-comp (F₁' f) (C.comp (F₁' g) (F₁' h))))
      ◃∙ F₁'-g-f (C.comp (F₁' f) (C.comp (F₁' g) (F₁' h))) ◃∎)
        =↯=⟨ 4 & 1 & ap (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁) (F₁'-g-f (C.comp (F₁' g) (F₁' h))) ◃∎
               & ∘-ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) F.F₁ (F₁'-g-f (C.comp (F₁' g) (F₁' h))) ⟩
      (ap F₁' (D.assoc f g h)
      ◃∙ ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! (D.comp g h))
      ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁) (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! g) (F₁'-f-g! h))
      ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁) (ap F₁' (! (F.pres-comp (F₁' g) (F₁' h))))
      ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁) (F₁'-g-f (C.comp (F₁' g) (F₁' h)))
      ◃∙ ap F₁' (! (F.pres-comp (F₁' f) (C.comp (F₁' g) (F₁' h))))
      ◃∙ F₁'-g-f (C.comp (F₁' f) (C.comp (F₁' g) (F₁' h))) ◃∎)
        =↯=⟨ 2 & 3 & ap (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁) (F₁'-pres-comp g h) ◃∎
               & ∙-ap-seq (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁) (F₁'-pres-comp-↯ g h) ⟩
      (ap F₁' (D.assoc f g h)
      ◃∙ ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! (D.comp g h))
      ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁) (F₁'-pres-comp g h)
      ◃∙ ap F₁' (! (F.pres-comp (F₁' f) (C.comp (F₁' g) (F₁' h))))
      ◃∙ F₁'-g-f (C.comp (F₁' f) (C.comp (F₁' g) (F₁' h))) ◃∎)
        =↯=⟨ 2 & 2 &
             homotopy-naturality-=ₛ
               (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁)
               (F₁' ∘ F.F₁ ∘ C.comp (F₁' f))
               (λ s → ap F₁' (! (F.pres-comp (F₁' f) s)))
               (F₁'-pres-comp g h) ⟩
      (ap F₁' (D.assoc f g h)
      ◃∙ ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! (D.comp g h))
      ◃∙ ap F₁' (! (F.pres-comp (F₁' f) (F₁' (D.comp g h))))
      ◃∙ ap (F₁' ∘ F.F₁ ∘ C.comp (F₁' f)) (F₁'-pres-comp g h)
      ◃∙ F₁'-g-f (C.comp (F₁' f) (C.comp (F₁' g) (F₁' h))) ◃∎)
        =↯=⟨ 3 & 2 &
             homotopy-naturality-=ₛ
               (F₁' ∘ F.F₁ ∘ C.comp (F₁' f))
               (C.comp (F₁' f))
               (F₁'-g-f ∘ C.comp (F₁' f))
               (F₁'-pres-comp g h) ⟩
      (ap F₁' (D.assoc f g h)
      ◃∙ ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! (D.comp g h))
      ◃∙ ap F₁' (! (F.pres-comp (F₁' f) (F₁' (D.comp g h))))
      ◃∙ F₁'-g-f (C.comp (F₁' f) (F₁' (D.comp g h)))
      ◃∙ ap (C.comp (F₁' f)) (F₁'-pres-comp g h) ◃∎)
        =↯=⟨ 1 & 3 & F₁'-pres-comp f (D.comp g h) ◃∎ & idp ⟩
      (ap F₁' (D.assoc f g h)
      ◃∙ F₁'-pres-comp f (D.comp g h)
      ◃∙ ap (C.comp (F₁' f)) (F₁'-pres-comp g h) ◃∎) ↯∎
      where
        step₅ : ap (λ s → F₁' (D.comp (F.F₁ s) (F.F₁ (F₁' h)))) (F₁'-g-f (C.comp (F₁' f) (F₁' g))) ◃∎
                =ₛ ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) (F₁'-f-g (F.F₁ (C.comp (F₁' f) (F₁' g)))) ◃∎
        step₅ = =ₛ-intro $
          ap (λ s → F₁' (D.comp (F.F₁ s) (F.F₁ (F₁' h)))) (F₁'-g-f (C.comp (F₁' f) (F₁' g)))
            =⟨ ap-∘ (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) F.F₁ (F₁'-g-f (C.comp (F₁' f) (F₁' g))) ⟩
          ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) (ap F.F₁ (F₁'-g-f (C.comp (F₁' f) (F₁' g))))
            =⟨ ap (ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))))
                  (is-equiv.adj (F₁-equiv (F₀ w) (F₀ y)) (C.comp (F₁' f) (F₁' g))) ⟩
          ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) (F₁'-f-g (F.F₁ (C.comp (F₁' f) (F₁' g)))) =∎
        step₈ : ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! (D.comp f g)) (F₁'-f-g! h) ◃∙
                ap (λ s → F₁' (D.comp (F.F₁ s) (F.F₁ (F₁' h)))) (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! g)) ◃∙
                ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) (F₁'-f-g (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g)))) ◃∎
                =ₛ
                ap (λ s → F₁' (D.comp (D.comp s g) h)) (F₁'-f-g! f) ◃∙
                ap (λ s → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) s) h)) (F₁'-f-g! g) ◃∙
                ap (λ s → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g))) s)) (F₁'-f-g! h) ◃∎
        step₈ = =ₛ-intro $
          (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! (D.comp f g)) (F₁'-f-g! h)
          ◃∙ ap (λ s → F₁' (D.comp (F.F₁ s) (F.F₁ (F₁' h)))) (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! g))
          ◃∙ ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) (F₁'-f-g (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g)))) ◃∎)
            =↯=⟨ 1 & 1 & (ap (λ s → F₁' (D.comp (F.F₁ s) (F.F₁ (F₁' h)))) (ap F₁' (ap2 D.comp (F₁'-f-g! f) (F₁'-f-g! g))) ◃∎)
                   & ap (ap (λ s → F₁' (D.comp (F.F₁ s) (F.F₁ (F₁' h)))))
                        (! (ap-ap2 F₁' D.comp (F₁'-f-g! f) (F₁'-f-g! g))) ⟩
          (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! (D.comp f g)) (F₁'-f-g! h)
          ◃∙ ap (λ s → F₁' (D.comp (F.F₁ s) (F.F₁ (F₁' h)))) (ap F₁' (ap2 D.comp (F₁'-f-g! f) (F₁'-f-g! g)))
          ◃∙ ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) (F₁'-f-g (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g)))) ◃∎)
            =↯=⟨ 1 & 1 & (ap (λ s → F₁' (D.comp (F.F₁ (F₁' s)) (F.F₁ (F₁' h)))) (ap2 D.comp (F₁'-f-g! f) (F₁'-f-g! g)) ◃∎)
                   & ∘-ap (λ s → F₁' (D.comp (F.F₁ s) (F.F₁ (F₁' h)))) F₁' (ap2 D.comp (F₁'-f-g! f) (F₁'-f-g! g)) ⟩
          (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! (D.comp f g)) (F₁'-f-g! h)
          ◃∙ ap (λ s → F₁' (D.comp (F.F₁ (F₁' s)) (F.F₁ (F₁' h)))) (ap2 D.comp (F₁'-f-g! f) (F₁'-f-g! g))
          ◃∙ ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) (F₁'-f-g (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g)))) ◃∎)
            =↯=⟨ 0 & 2 & !ₛ $
                 homotopy-naturality-=ₛ (λ s → F₁' (D.comp s h))
                                        (λ s → F₁' (D.comp (F.F₁ (F₁' s)) (F.F₁ (F₁' h))))
                                        (λ s → ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! s) (F₁'-f-g! h))
                                        (ap2 D.comp (F₁'-f-g! f) (F₁'-f-g! g)) ⟩
          (ap (λ s → F₁' (D.comp s h)) (ap2 D.comp (F₁'-f-g! f) (F₁'-f-g! g))
          ◃∙ ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g)))) (F₁'-f-g! h)
          ◃∙ ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) (F₁'-f-g (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g)))) ◃∎)
            =↯=⟨ 1 & 1 & (ap (λ t → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g))) t)) (F₁'-f-g! h)
                         ◃∙ ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) (F₁'-f-g! (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g)))) ◃∎)
                   & ap2-out' (λ s t → F₁' (D.comp s t)) (F₁'-f-g! (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g)))) (F₁'-f-g! h) ⟩
          (ap (λ s → F₁' (D.comp s h)) (ap2 D.comp (F₁'-f-g! f) (F₁'-f-g! g))
          ◃∙ ap (λ t → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g))) t)) (F₁'-f-g! h)
          ◃∙ ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) (F₁'-f-g! (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g))))
          ◃∙ ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) (F₁'-f-g (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g)))) ◃∎)
            =↯=⟨ 2 & 2 & (F₁' (D.comp (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g))) (F.F₁ (F₁' h))) ∎∎)
            & ap-seq-=↯= (λ s → F₁' (D.comp s (F.F₁ (F₁' h))))
                         (F₁'-f-g! (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g)))
                           ◃∙ F₁'-f-g (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g))) ◃∎)
                         (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g)) ∎∎)
                         (!-inv-l (F₁'-f-g (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g))))) ⟩
          (ap (λ s → F₁' (D.comp s h)) (ap2 D.comp (F₁'-f-g! f) (F₁'-f-g! g))
          ◃∙ ap (λ t → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g))) t)) (F₁'-f-g! h) ◃∎)
            =↯=⟨ 0 & 1 & (ap2 (λ s t → F₁' (D.comp (D.comp s t) h)) (F₁'-f-g! f) (F₁'-f-g! g) ◃∎)
                   & ap-ap2 (λ s → F₁' (D.comp s h)) D.comp (F₁'-f-g! f) (F₁'-f-g! g) ⟩
          (ap2 (λ s t → F₁' (D.comp (D.comp s t) h)) (F₁'-f-g! f) (F₁'-f-g! g)
          ◃∙ ap (λ t → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g))) t)) (F₁'-f-g! h) ◃∎)
            =↯=⟨ 0 & 1 & (ap (λ s → F₁' (D.comp (D.comp s g) h)) (F₁'-f-g! f)
                         ◃∙ ap (λ s → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) s) h)) (F₁'-f-g! g) ◃∎)
                   & ap2-out (λ s t → F₁' (D.comp (D.comp s t) h)) (F₁'-f-g! f) (F₁'-f-g! g) ⟩
          (ap (λ s → F₁' (D.comp (D.comp s g) h)) (F₁'-f-g! f)
          ◃∙ ap (λ s → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) s) h)) (F₁'-f-g! g)
          ◃∙ ap (λ s → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g))) s)) (F₁'-f-g! h) ◃∎) ↯∎
        step₁₀' : ap (λ s → D.comp s (F.F₁ (F₁' h))) (! (F.pres-comp (F₁' f) (F₁' g))) ◃∙
                  ! (F.pres-comp (C.comp (F₁' f) (F₁' g)) (F₁' h)) ◃∙
                  ap F.F₁ (C.assoc (F₁' f) (F₁' g) (F₁' h)) ◃∎
                  =ₛ
                  D.assoc (F.F₁ (F₁' f)) (F.F₁ (F₁' g)) (F.F₁ (F₁' h)) ◃∙
                  ap (D.comp (F.F₁ (F₁' f))) (! (F.pres-comp (F₁' g) (F₁' h))) ◃∙
                  ! (F.pres-comp (F₁' f) (C.comp (F₁' g) (F₁' h))) ◃∎
        step₁₀' = =ₛ-intro $
          (ap (λ s → D.comp s (F.F₁ (F₁' h))) (! (F.pres-comp (F₁' f) (F₁' g)))
          ◃∙ ! e₀₋₁
          ◃∙ e₀₋₄ ◃∎)
            =↯=⟨ 0 & 1 & ! (ap (λ s → D.comp s (F.F₁ (F₁' h))) (F.pres-comp (F₁' f) (F₁' g))) ◃∎
                    & ap-! (λ s → D.comp s (F.F₁ (F₁' h))) (F.pres-comp (F₁' f) (F₁' g)) ⟩
          (! e₁₋₂ ◃∙ ! e₀₋₁ ◃∙ e₀₋₄ ◃∎)
            ↯=⟨ post-rearrange-in (! e₁₋₂ ◃∙ ! e₀₋₁ ◃∙ e₀₋₄ ◃∎) (e₂₋₃ ◃∙ ! e₅₋₃ ◃∎) e₄₋₅ $
                post-rearrange-in (! e₁₋₂ ◃∙ ! e₀₋₁ ◃∙ e₀₋₄ ◃∙ e₄₋₅ ◃∎) (e₂₋₃ ◃∎) e₅₋₃ $
                pre-rotate'-in e₁₋₂ (! e₀₋₁ ∙ e₀₋₄ ∙ e₄₋₅ ∙ e₅₋₃) e₂₋₃ $
                pre-rotate'-in e₀₋₁ (e₀₋₄ ∙ e₄₋₅ ∙ e₅₋₃) (e₁₋₂ ∙ e₂₋₃) $
                ! (F.pres-comp-coh (F₁' f) (F₁' g) (F₁' h)) ⟩
          (e₂₋₃ ◃∙ ! e₅₋₃ ◃∙ ! e₄₋₅ ◃∎)
            =↯=⟨ 1 & 1 & ap (D.comp (F.F₁ (F₁' f))) (! (F.pres-comp (F₁' g) (F₁' h))) ◃∎
                    & !-ap (D.comp (F.F₁ (F₁' f))) (F.pres-comp (F₁' g) (F₁' h)) ⟩
          (e₂₋₃
          ◃∙ ap (D.comp (F.F₁ (F₁' f))) (! (F.pres-comp (F₁' g) (F₁' h)))
          ◃∙ ! e₄₋₅ ◃∎) ↯∎
          where
            t₀ : D.Arr (F.F₀ (F₀ w)) (F.F₀ (F₀ z))
            t₀ = F.F₁ (C.comp (C.comp (F₁' f) (F₁' g)) (F₁' h))
            t₁ : D.Arr (F.F₀ (F₀ w)) (F.F₀ (F₀ z))
            t₁ = D.comp (F.F₁ (C.comp (F₁' f) (F₁' g))) (F.F₁ (F₁' h))
            t₂ : D.Arr (F.F₀ (F₀ w)) (F.F₀ (F₀ z))
            t₂ = D.comp (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g))) (F.F₁ (F₁' h))
            t₃ : D.Arr (F.F₀ (F₀ w)) (F.F₀ (F₀ z))
            t₃ = D.comp (F.F₁ (F₁' f)) (D.comp (F.F₁ (F₁' g)) (F.F₁ (F₁' h)))
            t₄ : D.Arr (F.F₀ (F₀ w)) (F.F₀ (F₀ z))
            t₄ = F.F₁ (C.comp (F₁' f) (C.comp (F₁' g) (F₁' h)))
            t₅ = D.comp (F.F₁ (F₁' f)) (F.F₁ (C.comp (F₁' g) (F₁' h)))
            e₀₋₁ : t₀ == t₁
            e₀₋₁ = F.pres-comp (C.comp (F₁' f) (F₁' g)) (F₁' h)
            e₁₋₂ : t₁ == t₂
            e₁₋₂ = ap (λ s → D.comp s (F.F₁ (F₁' h))) (F.pres-comp (F₁' f) (F₁' g))
            e₂₋₃ : t₂ == t₃
            e₂₋₃ = D.assoc (F.F₁ (F₁' f)) (F.F₁ (F₁' g)) (F.F₁ (F₁' h))
            e₀₋₄ : t₀ == t₄
            e₀₋₄ = ap F.F₁ (C.assoc (F₁' f) (F₁' g) (F₁' h))
            e₄₋₅ : t₄ == t₅
            e₄₋₅ = F.pres-comp (F₁' f) (C.comp (F₁' g) (F₁' h))
            e₅₋₃ : t₅ == t₃
            e₅₋₃ = ap (D.comp (F.F₁ (F₁' f))) (F.pres-comp (F₁' g) (F₁' h))
        step₁₀ : ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) (! (F.pres-comp (F₁' f) (F₁' g))) ◃∙
                 ap F₁' (! (F.pres-comp (C.comp (F₁' f) (F₁' g)) (F₁' h))) ◃∙
                 ap (F₁' ∘ F.F₁) (C.assoc (F₁' f) (F₁' g) (F₁' h)) ◃∎
                 =ₛ
                 ap F₁' (D.assoc (F.F₁ (F₁' f)) (F.F₁ (F₁' g)) (F.F₁ (F₁' h))) ◃∙
                 ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (! (F.pres-comp (F₁' g) (F₁' h))) ◃∙
                 ap F₁' (! (F.pres-comp (F₁' f) (C.comp (F₁' g) (F₁' h)))) ◃∎
        step₁₀ = =ₛ-intro $
          (ap (λ s → F₁' (D.comp s (F.F₁ (F₁' h)))) (! (F.pres-comp (F₁' f) (F₁' g)))
          ◃∙ ap F₁' (! (F.pres-comp (C.comp (F₁' f) (F₁' g)) (F₁' h)))
          ◃∙ ap (F₁' ∘ F.F₁) (C.assoc (F₁' f) (F₁' g) (F₁' h)) ◃∎)
            =↯=⟨ 0 & 1 & ap F₁' (ap (λ s → D.comp s (F.F₁ (F₁' h))) (! (F.pres-comp (F₁' f) (F₁' g)))) ◃∎
                    & ap-∘ F₁' (λ s → D.comp s (F.F₁ (F₁' h))) (! (F.pres-comp (F₁' f) (F₁' g))) ⟩
          (ap F₁' (ap (λ s → D.comp s (F.F₁ (F₁' h))) (! (F.pres-comp (F₁' f) (F₁' g))))
          ◃∙ ap F₁' (! (F.pres-comp (C.comp (F₁' f) (F₁' g)) (F₁' h)))
          ◃∙ ap (F₁' ∘ F.F₁) (C.assoc (F₁' f) (F₁' g) (F₁' h)) ◃∎)
            =↯=⟨ 2 & 1 & ap F₁' (ap F.F₁ (C.assoc (F₁' f) (F₁' g) (F₁' h))) ◃∎
                    & ap-∘ F₁' F.F₁ (C.assoc (F₁' f) (F₁' g) (F₁' h)) ⟩
          (ap F₁' (ap (λ s → D.comp s (F.F₁ (F₁' h))) (! (F.pres-comp (F₁' f) (F₁' g))))
          ◃∙ ap F₁' (! (F.pres-comp (C.comp (F₁' f) (F₁' g)) (F₁' h)))
          ◃∙ ap F₁' (ap F.F₁ (C.assoc (F₁' f) (F₁' g) (F₁' h))) ◃∎)
            ↯=⟨ =ₛ-path (ap-seq-=ₛ F₁' step₁₀') ⟩
          (ap F₁' (D.assoc (F.F₁ (F₁' f)) (F.F₁ (F₁' g)) (F.F₁ (F₁' h)))
          ◃∙ ap F₁' (ap (D.comp (F.F₁ (F₁' f))) (! (F.pres-comp (F₁' g) (F₁' h))))
          ◃∙ ap F₁' (! (F.pres-comp (F₁' f) (C.comp (F₁' g) (F₁' h)))) ◃∎)
            =↯=⟨ 1 & 1 & ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (! (F.pres-comp (F₁' g) (F₁' h))) ◃∎
                    & ∘-ap F₁' (D.comp (F.F₁ (F₁' f))) (! (F.pres-comp (F₁' g) (F₁' h))) ⟩
          (ap F₁' (D.assoc (F.F₁ (F₁' f)) (F.F₁ (F₁' g)) (F.F₁ (F₁' h)))
          ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (! (F.pres-comp (F₁' g) (F₁' h)))
          ◃∙ ap F₁' (! (F.pres-comp (F₁' f) (C.comp (F₁' g) (F₁' h)))) ◃∎) ↯∎
        step₁₁ :
          ap (λ s → F₁' (D.comp (D.comp s g) h)) (F₁'-f-g! f) ◃∙
          ap (λ s → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) s) h)) (F₁'-f-g! g) ◃∙
          ap (λ s → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g))) s)) (F₁'-f-g! h) ◃∙
          ap F₁' (D.assoc (F.F₁ (F₁' f)) (F.F₁ (F₁' g)) (F.F₁ (F₁' h))) ◃∎
          =ₛ
          ap F₁' (D.assoc f g h) ◃∙
          ap (λ s → F₁' (D.comp s (D.comp g h))) (F₁'-f-g! f) ◃∙
          ap (λ s → F₁' (D.comp (F.F₁ (F₁' f)) (D.comp s h))) (F₁'-f-g! g) ◃∙
          ap (λ s → F₁' (D.comp (F.F₁ (F₁' f)) (D.comp (F.F₁ (F₁' g)) s))) (F₁'-f-g! h) ◃∎
        step₁₁ = =ₛ-intro $
          (ap (λ s → F₁' (D.comp (D.comp s g) h)) (F₁'-f-g! f)
          ◃∙ ap (λ s → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) s) h)) (F₁'-f-g! g)
          ◃∙ ap (λ s → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g))) s)) (F₁'-f-g! h)
          ◃∙ ap F₁' (D.assoc (F.F₁ (F₁' f)) (F.F₁ (F₁' g)) (F.F₁ (F₁' h))) ◃∎)
            =↯=⟨ 2 & 2 &
                 homotopy-naturality-=ₛ (λ s → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' g))) s))
                                        (λ s → F₁' (D.comp (F.F₁ (F₁' f)) (D.comp (F.F₁ (F₁' g)) s)))
                                        (λ s → ap F₁' (D.assoc (F.F₁ (F₁' f)) (F.F₁ (F₁' g)) s))
                                        (F₁'-f-g! h) ⟩
          (ap (λ s → F₁' (D.comp (D.comp s g) h)) (F₁'-f-g! f)
          ◃∙ ap (λ s → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) s) h)) (F₁'-f-g! g)
          ◃∙ ap F₁' (D.assoc (F.F₁ (F₁' f)) (F.F₁ (F₁' g)) h)
          ◃∙ ap (λ s → F₁' (D.comp (F.F₁ (F₁' f)) (D.comp (F.F₁ (F₁' g)) s))) (F₁'-f-g! h) ◃∎)
            =↯=⟨ 1 & 2 &
                 homotopy-naturality-=ₛ (λ s → F₁' (D.comp (D.comp (F.F₁ (F₁' f)) s) h))
                                        (λ s → F₁' (D.comp (F.F₁ (F₁' f)) (D.comp s h)))
                                        (λ s → ap F₁' (D.assoc (F.F₁ (F₁' f)) s h))
                                        (F₁'-f-g! g) ⟩
          (ap (λ s → F₁' (D.comp (D.comp s g) h)) (F₁'-f-g! f)
          ◃∙ ap F₁' (D.assoc (F.F₁ (F₁' f)) g h)
          ◃∙ ap (λ s → F₁' (D.comp (F.F₁ (F₁' f)) (D.comp s h))) (F₁'-f-g! g)
          ◃∙ ap (λ s → F₁' (D.comp (F.F₁ (F₁' f)) (D.comp (F.F₁ (F₁' g)) s))) (F₁'-f-g! h) ◃∎)
            =↯=⟨ 0 & 2 &
                 homotopy-naturality-=ₛ (λ s → F₁' (D.comp (D.comp s g) h))
                                        (λ s → F₁' (D.comp s (D.comp g h)))
                                        (λ s → ap F₁' (D.assoc s g h))
                                        (F₁'-f-g! f) ⟩
          (ap F₁' (D.assoc f g h)
          ◃∙ ap (λ s → F₁' (D.comp s (D.comp g h))) (F₁'-f-g! f)
          ◃∙ ap (λ s → F₁' (D.comp (F.F₁ (F₁' f)) (D.comp s h))) (F₁'-f-g! g)
          ◃∙ ap (λ s → F₁' (D.comp (F.F₁ (F₁' f)) (D.comp (F.F₁ (F₁' g)) s))) (F₁'-f-g! h) ◃∎) ↯∎
        step₁₂ : ap (λ s → F₁' (D.comp s (D.comp g h))) (F₁'-f-g! f) ◃∙
                 ap (λ s → F₁' (D.comp (F.F₁ (F₁' f)) (D.comp s h))) (F₁'-f-g! g) ◃∙
                 ap (λ s → F₁' (D.comp (F.F₁ (F₁' f)) (D.comp (F.F₁ (F₁' g)) s))) (F₁'-f-g! h) ◃∎
                 =ₛ
                 ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! (D.comp g h)) ◃∙
                 ap (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁) (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! g) (F₁'-f-g! h)) ◃∙
                 ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (F₁'-f-g (D.comp (F.F₁ (F₁' g)) (F.F₁ (F₁' h)))) ◃∎
        step₁₂ = =ₛ-intro $
          (ap (λ s → F₁' (D.comp s (D.comp g h))) (F₁'-f-g! f)
          ◃∙ ap (λ s → F₁' (D.comp (F.F₁ (F₁' f)) (D.comp s h))) (F₁'-f-g! g)
          ◃∙ ap (λ s → F₁' (D.comp (F.F₁ (F₁' f)) (D.comp (F.F₁ (F₁' g)) s))) (F₁'-f-g! h) ◃∎)
            =↯=⟨ 1 & 2 & ap2 (λ s t → F₁' (D.comp (F.F₁ (F₁' f)) (D.comp s t))) (F₁'-f-g! g) (F₁'-f-g! h) ◃∎
                    & ! (ap2-out (λ s t → F₁' (D.comp (F.F₁ (F₁' f)) (D.comp s t))) (F₁'-f-g! g) (F₁'-f-g! h)) ⟩
          (ap (λ s → F₁' (D.comp s (D.comp g h))) (F₁'-f-g! f)
          ◃∙ ap2 (λ s t → F₁' (D.comp (F.F₁ (F₁' f)) (D.comp s t))) (F₁'-f-g! g) (F₁'-f-g! h) ◃∎)
            =↯=⟨ 1 & 1 & ap (λ s → F₁' (D.comp (F.F₁ (F₁' f)) s)) (ap2 D.comp (F₁'-f-g! g) (F₁'-f-g! h)) ◃∎
                    & ! (ap-ap2 (F₁' ∘ D.comp (F.F₁ (F₁' f))) D.comp (F₁'-f-g! g) (F₁'-f-g! h)) ⟩
          (ap (λ s → F₁' (D.comp s (D.comp g h))) (F₁'-f-g! f)
          ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (ap2 D.comp (F₁'-f-g! g) (F₁'-f-g! h)) ◃∎)
            =↯=⟨ 2 & 0 & (ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (F₁'-f-g! (D.comp (F.F₁ (F₁' g)) (F.F₁ (F₁' h))))
                          ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (F₁'-f-g (D.comp (F.F₁ (F₁' g)) (F.F₁ (F₁' h)))) ◃∎)
                    & ap-seq-=↯= (F₁' ∘ D.comp (F.F₁ (F₁' f)))
                                (D.comp (F.F₁ (F₁' g)) (F.F₁ (F₁' h)) ∎∎)
                                (F₁'-f-g! (D.comp (F.F₁ (F₁' g)) (F.F₁ (F₁' h)))
                                  ◃∙ F₁'-f-g (D.comp (F.F₁ (F₁' g)) (F.F₁ (F₁' h))) ◃∎)
                                (! (!-inv-l (F₁'-f-g (D.comp (F.F₁ (F₁' g)) (F.F₁ (F₁' h)))))) ⟩
          (ap (λ s → F₁' (D.comp s (D.comp g h))) (F₁'-f-g! f)
          ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (ap2 D.comp (F₁'-f-g! g) (F₁'-f-g! h))
          ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (F₁'-f-g! (D.comp (F.F₁ (F₁' g)) (F.F₁ (F₁' h))))
          ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (F₁'-f-g (D.comp (F.F₁ (F₁' g)) (F.F₁ (F₁' h)))) ◃∎)
            =↯=⟨ 1 & 2 &
                 homotopy-naturality-=ₛ (F₁' ∘ D.comp (F.F₁ (F₁' f)))
                                        (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁ ∘ F₁')
                                        (ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) ∘ F₁'-f-g!)
                                        (ap2 D.comp (F₁'-f-g! g) (F₁'-f-g! h)) ⟩
          (ap (λ s → F₁' (D.comp s (D.comp g h))) (F₁'-f-g! f)
          ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (F₁'-f-g! (D.comp g h))
          ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁ ∘ F₁') (ap2 D.comp (F₁'-f-g! g) (F₁'-f-g! h))
          ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (F₁'-f-g (D.comp (F.F₁ (F₁' g)) (F.F₁ (F₁' h)))) ◃∎)
            =↯=⟨ 0 & 2 & ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! (D.comp g h)) ◃∎
                    & ! (ap2-out (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! (D.comp g h))) ⟩
          (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! (D.comp g h))
          ◃∙ ap (λ s → F₁' (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' s)))) (ap2 D.comp (F₁'-f-g! g) (F₁'-f-g! h))
          ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (F₁'-f-g (D.comp (F.F₁ (F₁' g)) (F.F₁ (F₁' h)))) ◃∎)
            =↯=⟨ 1 & 1 & ap2 (λ s t → F₁' (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' (D.comp s t))))) (F₁'-f-g! g) (F₁'-f-g! h) ◃∎
                    & ap-ap2 (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁ ∘ F₁')
                            D.comp (F₁'-f-g! g) (F₁'-f-g! h) ⟩
          (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! (D.comp g h))
          ◃∙ ap2 (λ s t → F₁' (D.comp (F.F₁ (F₁' f)) (F.F₁ (F₁' (D.comp s t))))) (F₁'-f-g! g) (F₁'-f-g! h)
          ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (F₁'-f-g (D.comp (F.F₁ (F₁' g)) (F.F₁ (F₁' h)))) ◃∎)
            =↯=⟨ 1 & 1 & ap (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁) (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! g) (F₁'-f-g! h)) ◃∎
                    & ! (ap-ap2 (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁)
                                (λ s t → F₁' (D.comp s t))
                                (F₁'-f-g! g)
                                (F₁'-f-g! h)) ⟩
          (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! f) (F₁'-f-g! (D.comp g h))
          ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f)) ∘ F.F₁) (ap2 (λ s t → F₁' (D.comp s t)) (F₁'-f-g! g) (F₁'-f-g! h))
          ◃∙ ap (F₁' ∘ D.comp (F.F₁ (F₁' f))) (F₁'-f-g (D.comp (F.F₁ (F₁' g)) (F.F₁ (F₁' h)))) ◃∎) ↯∎
    F₁''-pres-comp-coh {w} {x} {y} {z} f g h =
      coe-comp-coh D.comp D.assoc (F₀-f-g w) (F₀-f-g x) (F₀-f-g y) (F₀-f-g z) f g h
    pres-comp-coh : {w x y z : D.El}
      (f : D.Arr w x) (g : D.Arr x y) (h : D.Arr y z)
      → pres-comp (D.comp f g) h ∙ ap (λ s → C.comp s (F₁ h)) (pres-comp f g) ∙ C.assoc (F₁ f) (F₁ g) (F₁ h)
        == ap F₁ (D.assoc f g h) ∙ pres-comp f (D.comp g h) ∙ ap (C.comp (F₁ f)) (pres-comp g h)
    pres-comp-coh f g h =
      (pres-comp (D.comp f g) h ◃∙ ap (λ s → C.comp s (F₁ h)) (pres-comp f g) ◃∙ C.assoc (F₁ f) (F₁ g) (F₁ h) ◃∎)
        =↯=⟨ 0 & 1 & pres-comp-↯ (D.comp f g) h & idp ⟩
      (ap F₁' (F₁''-pres-comp (D.comp f g) h)
      ◃∙ F₁'-pres-comp (F₁'' (D.comp f g)) (F₁'' h)
      ◃∙ ap (λ s → C.comp s (F₁ h)) (pres-comp f g)
      ◃∙ C.assoc (F₁ f) (F₁ g) (F₁ h) ◃∎)
        =↯=⟨ 2 & 1 & ap-seq (λ s → C.comp s (F₁ h)) (pres-comp-↯ f g)
               & ap-seq-∙ (λ s → C.comp s (F₁ h)) (pres-comp-↯ f g) ⟩
      (ap F₁' (F₁''-pres-comp (D.comp f g) h)
      ◃∙ F₁'-pres-comp (F₁'' (D.comp f g)) (F₁'' h)
      ◃∙ ap (λ s → C.comp s (F₁ h)) (ap F₁' (F₁''-pres-comp f g))
      ◃∙ ap (λ s → C.comp s (F₁ h)) (F₁'-pres-comp (F₁'' f) (F₁'' g))
      ◃∙ C.assoc (F₁ f) (F₁ g) (F₁ h) ◃∎)
        =↯=⟨ 2 & 1 & ap (λ s → C.comp (F₁' s) (F₁ h)) (F₁''-pres-comp f g) ◃∎
               & ∘-ap (λ s → C.comp s (F₁ h)) F₁' (F₁''-pres-comp f g) ⟩
      (ap F₁' (F₁''-pres-comp (D.comp f g) h)
      ◃∙ F₁'-pres-comp (F₁'' (D.comp f g)) (F₁'' h)
      ◃∙ ap (λ s → C.comp (F₁' s) (F₁ h)) (F₁''-pres-comp f g)
      ◃∙ ap (λ s → C.comp s (F₁ h)) (F₁'-pres-comp (F₁'' f) (F₁'' g))
      ◃∙ C.assoc (F₁ f) (F₁ g) (F₁ h) ◃∎)
        =↯=⟨ 1 & 2 & !ₛ $
             homotopy-naturality-=ₛ (λ s → F₁' (D.comp s (F₁'' h)))
                                    (λ s → C.comp (F₁' s) (F₁ h))
                                    (λ s → F₁'-pres-comp s (F₁'' h))
                                    (F₁''-pres-comp f g) ⟩
      (ap F₁' (F₁''-pres-comp (D.comp f g) h)
      ◃∙ ap (λ s → F₁' (D.comp s (F₁'' h))) (F₁''-pres-comp f g)
      ◃∙ F₁'-pres-comp (D.comp (F₁'' f) (F₁'' g)) (F₁'' h)
      ◃∙ ap (λ s → C.comp s (F₁ h)) (F₁'-pres-comp (F₁'' f) (F₁'' g))
      ◃∙ C.assoc (F₁ f) (F₁ g) (F₁ h) ◃∎)
        =↯=⟨ 2 & 3 & (ap F₁' (D.assoc (F₁'' f) (F₁'' g) (F₁'' h))
                     ◃∙ F₁'-pres-comp (F₁'' f) (D.comp (F₁'' g) (F₁'' h))
                     ◃∙ ap (C.comp (F₁ f)) (F₁'-pres-comp (F₁'' g) (F₁'' h)) ◃∎)
               & F₁'-pres-comp-coh (F₁'' f) (F₁'' g) (F₁'' h) ⟩
      (ap F₁' (F₁''-pres-comp (D.comp f g) h)
      ◃∙ ap (λ s → F₁' (D.comp s (F₁'' h))) (F₁''-pres-comp f g)
      ◃∙ ap F₁' (D.assoc (F₁'' f) (F₁'' g) (F₁'' h))
      ◃∙ F₁'-pres-comp (F₁'' f) (D.comp (F₁'' g) (F₁'' h))
      ◃∙ ap (C.comp (F₁ f)) (F₁'-pres-comp (F₁'' g) (F₁'' h)) ◃∎)
        =↯=⟨ 1 & 1 & ap F₁' (ap (λ s → D.comp s (F₁'' h)) (F₁''-pres-comp f g)) ◃∎
               & ap-∘ F₁' (λ s → D.comp s (F₁'' h)) (F₁''-pres-comp f g) ⟩
      (ap F₁' (F₁''-pres-comp (D.comp f g) h)
      ◃∙ ap F₁' (ap (λ s → D.comp s (F₁'' h)) (F₁''-pres-comp f g))
      ◃∙ ap F₁' (D.assoc (F₁'' f) (F₁'' g) (F₁'' h))
      ◃∙ F₁'-pres-comp (F₁'' f) (D.comp (F₁'' g) (F₁'' h))
      ◃∙ ap (C.comp (F₁ f)) (F₁'-pres-comp (F₁'' g) (F₁'' h)) ◃∎)
        =↯=⟨ 0 & 3 & (ap F₁' (ap F₁'' (D.assoc f g h))
                     ◃∙ ap F₁' (F₁''-pres-comp f (D.comp g h))
                     ◃∙ ap F₁' (ap (D.comp (F₁'' f)) (F₁''-pres-comp g h)) ◃∎)
               & ap-seq-=↯= F₁'
                   (F₁''-pres-comp (D.comp f g) h
                     ◃∙ ap (λ s → D.comp s (F₁'' h)) (F₁''-pres-comp f g)
                     ◃∙ D.assoc (F₁'' f) (F₁'' g) (F₁'' h) ◃∎)
                   (ap F₁'' (D.assoc f g h)
                     ◃∙ F₁''-pres-comp f (D.comp g h)
                     ◃∙ ap (D.comp (F₁'' f)) (F₁''-pres-comp g h) ◃∎)
                   (F₁''-pres-comp-coh f g h) ⟩
      (ap F₁' (ap F₁'' (D.assoc f g h))
      ◃∙ ap F₁' (F₁''-pres-comp f (D.comp g h))
      ◃∙ ap F₁' (ap (D.comp (F₁'' f)) (F₁''-pres-comp g h))
      ◃∙ F₁'-pres-comp (F₁'' f) (D.comp (F₁'' g) (F₁'' h))
      ◃∙ ap (C.comp (F₁ f)) (F₁'-pres-comp (F₁'' g) (F₁'' h)) ◃∎)
        =↯=⟨ 2 & 1 & ap (F₁' ∘ D.comp (F₁'' f)) (F₁''-pres-comp g h) ◃∎
               & ∘-ap F₁' (D.comp (F₁'' f)) (F₁''-pres-comp g h) ⟩
      (ap F₁' (ap F₁'' (D.assoc f g h))
      ◃∙ ap F₁' (F₁''-pres-comp f (D.comp g h))
      ◃∙ ap (F₁' ∘ D.comp (F₁'' f)) (F₁''-pres-comp g h)
      ◃∙ F₁'-pres-comp (F₁'' f) (D.comp (F₁'' g) (F₁'' h))
      ◃∙ ap (C.comp (F₁ f)) (F₁'-pres-comp (F₁'' g) (F₁'' h)) ◃∎)
        =↯=⟨ 2 & 2 &
             homotopy-naturality-=ₛ (F₁' ∘ D.comp (F₁'' f))
                                    (C.comp (F₁ f) ∘ F₁')
                                    (F₁'-pres-comp (F₁'' f))
                                    (F₁''-pres-comp g h) ⟩
      (ap F₁' (ap F₁'' (D.assoc f g h))
      ◃∙ ap F₁' (F₁''-pres-comp f (D.comp g h))
      ◃∙ F₁'-pres-comp (F₁'' f) (F₁'' (D.comp g h))
      ◃∙ ap (C.comp (F₁ f) ∘ F₁') (F₁''-pres-comp g h)
      ◃∙ ap (C.comp (F₁ f)) (F₁'-pres-comp (F₁'' g) (F₁'' h)) ◃∎)
        =↯=⟨ 1 & 2 & pres-comp f (D.comp g h) ◃∎ & idp ⟩
      (ap F₁' (ap F₁'' (D.assoc f g h))
      ◃∙ pres-comp f (D.comp g h)
      ◃∙ ap (C.comp (F₁ f) ∘ F₁') (F₁''-pres-comp g h)
      ◃∙ ap (C.comp (F₁ f)) (F₁'-pres-comp (F₁'' g) (F₁'' h)) ◃∎)
        =↯=⟨ 2 & 1 & ap (C.comp (F₁ f)) (ap F₁' (F₁''-pres-comp g h)) ◃∎
               & ap-∘ (C.comp (F₁ f)) F₁' (F₁''-pres-comp g h) ⟩
      (ap F₁' (ap F₁'' (D.assoc f g h))
      ◃∙ pres-comp f (D.comp g h)
      ◃∙ ap (C.comp (F₁ f)) (ap F₁' (F₁''-pres-comp g h))
      ◃∙ ap (C.comp (F₁ f)) (F₁'-pres-comp (F₁'' g) (F₁'' h)) ◃∎)
        =↯=⟨ 2 & 2 & ap (C.comp (F₁ f)) (pres-comp g h) ◃∎
               & ∙-ap-seq (C.comp (F₁ f)) (pres-comp-↯ g h) ⟩
      (ap F₁' (ap F₁'' (D.assoc f g h))
      ◃∙ pres-comp f (D.comp g h)
      ◃∙ ap (C.comp (F₁ f)) (pres-comp g h) ◃∎)
        =↯=⟨ 0 & 1 & ap F₁ (D.assoc f g h) ◃∎
               & ∘-ap F₁' F₁'' (D.assoc f g h) ⟩
      (ap F₁ (D.assoc f g h) ◃∙ pres-comp f (D.comp g h) ◃∙ ap (C.comp (F₁ f)) (pres-comp g h) ◃∎) ↯∎
