{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
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
    → coe-comp p p'' p''' (comp f g) h ◃∙
      ap (λ s → comp s (coe-C p'' p''' h)) (coe-comp p p' p'' f g) ◃∙
      assoc (coe-C p p' f) (coe-C p' p'' g) (coe-C p'' p''' h) ◃∎
      =ₛ
      ap (coe-C p p''') (assoc f g h) ◃∙
      coe-comp p p' p''' f (comp g h) ◃∙
      ap (comp (coe-C p p' f)) (coe-comp p' p'' p''' g h) ◃∎
  coe-comp-coh assoc idp idp idp idp f g h = =ₛ-in $
    ! (ap-idf (assoc f g h)) ∙ ! (∙-unit-r (ap (coe-C idp idp) (assoc f g h)))

module FunctorInverse
  {i₁ j₁ i₂ j₂}
  {C : TwoSemiCategory i₁ j₁} {D : TwoSemiCategory i₂ j₂}
  (F : TwoSemiFunctor C D)
  (F₀-is-equiv : is-equiv (TwoSemiFunctor.F₀ F))
  (F₁-is-equiv : ∀ x y → is-equiv (TwoSemiFunctor.F₁ F {x} {y})) where

  private

    module C = TwoSemiCategory C
    module D = TwoSemiCategory D
    module F = TwoSemiFunctor F

    module F₀-is-equiv = is-equiv F₀-is-equiv
    module F₁-is-equiv (x y : C.El) = is-equiv (F₁-is-equiv x y)

    F₀ = F.F₀
    F₁ = F.F₁

  G₀ : D.El → C.El
  G₀ = F₀-is-equiv.g

  D' : TwoSemiCategory i₂ j₂
  D' =
    record
    { El = D.El
    ; Arr = λ x y → D.Arr (F₀ (G₀ x)) (F₀ (G₀ y))
    ; Arr-level = λ x y → D.Arr-level (F₀ (G₀ x)) (F₀ (G₀ y))
    ; two-semi-cat-struct =
      record
      { comp = λ f g → D.comp f g
      ; assoc = λ f g h → D.assoc f g h
      ; pentagon-identity = λ f g h i → D.pentagon-identity f g h i
      }
    }

  N : TwoSemiFunctor D D'
  N =
    record
    { F₀ = idf D.El
    ; F₁ = λ {x} {y} f → coe (Arr-path x y) f
    ; pres-comp = λ {x} {y} {z} f g →
        coe-comp D.comp (F₀-η x) (F₀-η y) (F₀-η z) f g
    ; pres-comp-coh = λ {w} {x} {y} {z} f g h →
        coe-comp-coh D.comp D.assoc (F₀-η w) (F₀-η x) (F₀-η y) (F₀-η z) f g h
    }
    where
    F₀-η : (x : D.El) → x == F₀ (G₀ x)
    F₀-η x = ! (F₀-is-equiv.f-g x)
    Arr-path : (x y : D.El) → D.Arr x y == D.Arr (F₀ (G₀ x)) (F₀ (G₀ y))
    Arr-path x y = ap2 D.Arr (F₀-η x) (F₀-η y)

  module N = TwoSemiFunctor N

  G₁ : {x y : D.El} → D.Arr (F₀ (G₀ x)) (F₀ (G₀ y)) → C.Arr (G₀ x) (G₀ y)
  G₁ {x} {y} f = F₁-is-equiv.g (G₀ x) (G₀ y) f

  F₁-β : {x y : D.El} (f : D.Arr (F₀ (G₀ x)) (F₀ (G₀ y)))
    → F₁ (G₁ f) == f
  F₁-β {x} {y} f = F₁-is-equiv.f-g (G₀ x) (G₀ y) f

  F₁-η : {x y : D.El} (f : D.Arr (F₀ (G₀ x)) (F₀ (G₀ y)))
    → f == F₁ (G₁ f)
  F₁-η f = ! (F₁-β f)

  G₁-β : {x y : D.El} → (f : C.Arr (G₀ x) (G₀ y))
    → G₁ (F₁ f) == f
  G₁-β {x} {y} f = F₁-is-equiv.g-f (G₀ x) (G₀ y) f

  G₁-pres-comp-seq : {x y z : D.El}
    (f : D.Arr (F₀ (G₀ x)) (F₀ (G₀ y)))
    (g : D.Arr (F₀ (G₀ y)) (F₀ (G₀ z)))
    → G₁ (D.comp f g) =-= C.comp (G₁ f) (G₁ g)
  G₁-pres-comp-seq {x} {y} {z} f g =
    G₁ (D.comp f g)
      =⟪ ap2 (λ s t → G₁ (D.comp s t)) (F₁-η f) (F₁-η g) ⟫
    G₁ (D.comp (F₁ (G₁ f)) (F₁ (G₁ g)))
      =⟪ ap G₁ (! (F.pres-comp (G₁ f) (G₁ g))) ⟫
    G₁ (F₁ (C.comp (G₁ f) (G₁ g)))
      =⟪ G₁-β (C.comp (G₁ f) (G₁ g)) ⟫
    C.comp (G₁ f) (G₁ g) ∎∎

  abstract
    G₁-pres-comp : {x y z : D.El}
      (f : D.Arr (F₀ (G₀ x)) (F₀ (G₀ y)))
      (g : D.Arr (F₀ (G₀ y)) (F₀ (G₀ z)))
      → G₁ (D.comp f g) == C.comp (G₁ f) (G₁ g)
    G₁-pres-comp f g = ↯ (G₁-pres-comp-seq f g)

    G₁-pres-comp-β : {x y z : D.El}
      (f : D.Arr (F₀ (G₀ x)) (F₀ (G₀ y)))
      (g : D.Arr (F₀ (G₀ y)) (F₀ (G₀ z)))
      → G₁-pres-comp f g ◃∎ =ₛ G₁-pres-comp-seq f g
    G₁-pres-comp-β f g = =ₛ-in idp

  private
    G₁-pres-comp-coh : {w x y z : D.El}
      (f : D.Arr (F₀ (G₀ w)) (F₀ (G₀ x)))
      (g : D.Arr (F₀ (G₀ x)) (F₀ (G₀ y)))
      (h : D.Arr (F₀ (G₀ y)) (F₀ (G₀ z)))
      → G₁-pres-comp (D.comp f g) h ◃∙
        ap (λ s → C.comp s (G₁ h)) (G₁-pres-comp f g) ◃∙
        C.assoc (G₁ f) (G₁ g) (G₁ h) ◃∎
        =ₛ
        ap G₁ (D.assoc f g h) ◃∙
        G₁-pres-comp f (D.comp g h) ◃∙
        ap (C.comp (G₁ f)) (G₁-pres-comp g h) ◃∎
    G₁-pres-comp-coh {w} {x} {y} {z} f g h =
      G₁-pres-comp (D.comp f g) h ◃∙
      ap (λ s → C.comp s (G₁ h)) (G₁-pres-comp f g) ◃∙
      C.assoc (G₁ f) (G₁ g) (G₁ h) ◃∎
        =ₛ⟨ 0 & 1 & G₁-pres-comp-β (D.comp f g) h ⟩
      ap2 (λ s t → G₁ (D.comp s t)) (F₁-η (D.comp f g)) (F₁-η h) ◃∙
      ap G₁ (! (F.pres-comp (G₁ (D.comp f g)) (G₁ h))) ◃∙
      G₁-β (C.comp (G₁ (D.comp f g)) (G₁ h)) ◃∙
      ap (λ s → C.comp s (G₁ h)) (G₁-pres-comp f g) ◃∙
      C.assoc (G₁ f) (G₁ g) (G₁ h) ◃∎
        =ₛ⟨ 2 & 2 & !ₛ $
            homotopy-naturality
              (λ s → G₁ (F₁ (C.comp s (G₁ h))))
              (λ s → C.comp s (G₁ h))
              (λ s → G₁-β (C.comp s (G₁ h)))
              (G₁-pres-comp f g) ⟩
      ap2 (λ s t → G₁ (D.comp s t)) (F₁-η (D.comp f g)) (F₁-η h) ◃∙
      ap G₁ (! (F.pres-comp (G₁ (D.comp f g)) (G₁ h))) ◃∙
      ap (λ s → G₁ (F₁ (C.comp s (G₁ h)))) (G₁-pres-comp f g) ◃∙
      G₁-β (C.comp (C.comp (G₁ f) (G₁ g)) (G₁ h)) ◃∙
      C.assoc (G₁ f) (G₁ g) (G₁ h) ◃∎
        =ₛ⟨ 1 & 2 & !ₛ $
            homotopy-naturality
              (λ s → G₁ (D.comp (F₁ s) (F₁ (G₁ h))))
              (λ s → G₁ (F₁ (C.comp s (G₁ h))))
              (λ s → ap G₁ (! (F.pres-comp s (G₁ h))))
              (G₁-pres-comp f g) ⟩
      ap2 (λ s t → G₁ (D.comp s t)) (F₁-η (D.comp f g)) (F₁-η h) ◃∙
      ap (λ s → G₁ (D.comp (F₁ s) (F₁ (G₁ h)))) (G₁-pres-comp f g) ◃∙
      ap G₁ (! (F.pres-comp (C.comp (G₁ f) (G₁ g)) (G₁ h))) ◃∙
      G₁-β (C.comp (C.comp (G₁ f) (G₁ g)) (G₁ h)) ◃∙
      C.assoc (G₁ f) (G₁ g) (G₁ h) ◃∎
        =ₛ⟨ 1 & 1 & ap-seq-=ₛ (λ s → G₁ (D.comp (F₁ s) (F₁ (G₁ h)))) (G₁-pres-comp-β f g) ⟩
      ap2 (λ s t → G₁ (D.comp s t)) (F₁-η (D.comp f g)) (F₁-η h) ◃∙
      ap (λ s → G₁ (D.comp (F₁ s) (F₁ (G₁ h)))) (ap2 (λ s t → G₁ (D.comp s t)) (F₁-η f) (F₁-η g)) ◃∙
      ap (λ s → G₁ (D.comp (F₁ s) (F₁ (G₁ h)))) (ap G₁ (! (F.pres-comp (G₁ f) (G₁ g)))) ◃∙
      ap (λ s → G₁ (D.comp (F₁ s) (F₁ (G₁ h)))) (G₁-β (C.comp (G₁ f) (G₁ g))) ◃∙
      ap G₁ (! (F.pres-comp (C.comp (G₁ f) (G₁ g)) (G₁ h))) ◃∙
      G₁-β (C.comp (C.comp (G₁ f) (G₁ g)) (G₁ h)) ◃∙
      C.assoc (G₁ f) (G₁ g) (G₁ h) ◃∎
        =ₛ₁⟨ 3 & 1 & step₅ ⟩
      ap2 (λ s t → G₁ (D.comp s t)) (F₁-η (D.comp f g)) (F₁-η h) ◃∙
      ap (λ s → G₁ (D.comp (F₁ s) (F₁ (G₁ h)))) (ap2 (λ s t → G₁ (D.comp s t)) (F₁-η f) (F₁-η g)) ◃∙
      ap (λ s → G₁ (D.comp (F₁ s) (F₁ (G₁ h)))) (ap G₁ (! (F.pres-comp (G₁ f) (G₁ g)))) ◃∙
      ap (λ s → G₁ (D.comp s (F₁ (G₁ h)))) (F₁-β (F₁ (C.comp (G₁ f) (G₁ g)))) ◃∙
      ap G₁ (! (F.pres-comp (C.comp (G₁ f) (G₁ g)) (G₁ h))) ◃∙
      G₁-β (C.comp (C.comp (G₁ f) (G₁ g)) (G₁ h)) ◃∙
      C.assoc (G₁ f) (G₁ g) (G₁ h) ◃∎
        =ₛ₁⟨ 2 & 1 & ∘-ap (λ s → G₁ (D.comp (F₁ s) (F₁ (G₁ h)))) G₁ (! (F.pres-comp (G₁ f) (G₁ g))) ⟩
      ap2 (λ s t → G₁ (D.comp s t)) (F₁-η (D.comp f g)) (F₁-η h) ◃∙
      ap (λ s → G₁ (D.comp (F₁ s) (F₁ (G₁ h)))) (ap2 (λ s t → G₁ (D.comp s t)) (F₁-η f) (F₁-η g)) ◃∙
      ap (λ s → G₁ (D.comp (F₁ (G₁ s)) (F₁ (G₁ h)))) (! (F.pres-comp (G₁ f) (G₁ g))) ◃∙
      ap (λ s → G₁ (D.comp s (F₁ (G₁ h)))) (F₁-β (F₁ (C.comp (G₁ f) (G₁ g)))) ◃∙
      ap G₁ (! (F.pres-comp (C.comp (G₁ f) (G₁ g)) (G₁ h))) ◃∙
      G₁-β (C.comp (C.comp (G₁ f) (G₁ g)) (G₁ h)) ◃∙
      C.assoc (G₁ f) (G₁ g) (G₁ h) ◃∎
        =ₛ⟨ 2 & 2 & homotopy-naturality
                      (λ s → G₁ (D.comp (F₁ (G₁ s)) (F₁ (G₁ h))))
                      (λ s → G₁ (D.comp s (F₁ (G₁ h))))
                      (λ t → ap (λ s → G₁ (D.comp s (F₁ (G₁ h)))) (F₁-β t))
                      (! (F.pres-comp (G₁ f) (G₁ g))) ⟩
      ap2 (λ s t → G₁ (D.comp s t)) (F₁-η (D.comp f g)) (F₁-η h) ◃∙
      ap (λ s → G₁ (D.comp (F₁ s) (F₁ (G₁ h)))) (ap2 (λ s t → G₁ (D.comp s t)) (F₁-η f) (F₁-η g)) ◃∙
      ap (λ s → G₁ (D.comp s (F₁ (G₁ h)))) (F₁-β (D.comp (F₁ (G₁ f)) (F₁ (G₁ g)))) ◃∙
      ap (λ s → G₁ (D.comp s (F₁ (G₁ h)))) (! (F.pres-comp (G₁ f) (G₁ g))) ◃∙
      ap G₁ (! (F.pres-comp (C.comp (G₁ f) (G₁ g)) (G₁ h))) ◃∙
      G₁-β (C.comp (C.comp (G₁ f) (G₁ g)) (G₁ h)) ◃∙
      C.assoc (G₁ f) (G₁ g) (G₁ h) ◃∎
        =ₛ⟨ 0 & 3 & step₈ ⟩
      ap (λ s → G₁ (D.comp (D.comp s g) h)) (F₁-η f) ◃∙
      ap (λ s → G₁ (D.comp (D.comp (F₁ (G₁ f)) s) h)) (F₁-η g) ◃∙
      ap (λ s → G₁ (D.comp (D.comp (F₁ (G₁ f)) (F₁ (G₁ g))) s)) (F₁-η h) ◃∙
      ap (λ s → G₁ (D.comp s (F₁ (G₁ h)))) (! (F.pres-comp (G₁ f) (G₁ g))) ◃∙
      ap G₁ (! (F.pres-comp (C.comp (G₁ f) (G₁ g)) (G₁ h))) ◃∙
      G₁-β (C.comp (C.comp (G₁ f) (G₁ g)) (G₁ h)) ◃∙
      C.assoc (G₁ f) (G₁ g) (G₁ h) ◃∎
        =ₛ⟨ 5 & 2 & !ₛ $
            homotopy-naturality-to-idf (G₁ ∘ F₁) G₁-β (C.assoc (G₁ f) (G₁ g) (G₁ h)) ⟩
      ap (λ s → G₁ (D.comp (D.comp s g) h)) (F₁-η f) ◃∙
      ap (λ s → G₁ (D.comp (D.comp (F₁ (G₁ f)) s) h)) (F₁-η g) ◃∙
      ap (λ s → G₁ (D.comp (D.comp (F₁ (G₁ f)) (F₁ (G₁ g))) s)) (F₁-η h) ◃∙
      ap (λ s → G₁ (D.comp s (F₁ (G₁ h)))) (! (F.pres-comp (G₁ f) (G₁ g))) ◃∙
      ap G₁ (! (F.pres-comp (C.comp (G₁ f) (G₁ g)) (G₁ h))) ◃∙
      ap (G₁ ∘ F₁) (C.assoc (G₁ f) (G₁ g) (G₁ h)) ◃∙
      G₁-β (C.comp (G₁ f) (C.comp (G₁ g) (G₁ h))) ◃∎
        =ₛ⟨ 3 & 3 & step₁₀ ⟩
      ap (λ s → G₁ (D.comp (D.comp s g) h)) (F₁-η f) ◃∙
      ap (λ s → G₁ (D.comp (D.comp (F₁ (G₁ f)) s) h)) (F₁-η g) ◃∙
      ap (λ s → G₁ (D.comp (D.comp (F₁ (G₁ f)) (F₁ (G₁ g))) s)) (F₁-η h) ◃∙
      ap G₁ (D.assoc (F₁ (G₁ f)) (F₁ (G₁ g)) (F₁ (G₁ h))) ◃∙
      ap (G₁ ∘ D.comp (F₁ (G₁ f))) (! (F.pres-comp (G₁ g) (G₁ h))) ◃∙
      ap G₁ (! (F.pres-comp (G₁ f) (C.comp (G₁ g) (G₁ h)))) ◃∙
      G₁-β (C.comp (G₁ f) (C.comp (G₁ g) (G₁ h))) ◃∎
        =ₛ⟨ 0 & 4 & step₁₁ ⟩
      ap G₁ (D.assoc f g h) ◃∙
      ap (λ s → G₁ (D.comp s (D.comp g h))) (F₁-η f) ◃∙
      ap (λ s → G₁ (D.comp (F₁ (G₁ f)) (D.comp s h))) (F₁-η g) ◃∙
      ap (λ s → G₁ (D.comp (F₁ (G₁ f)) (D.comp (F₁ (G₁ g)) s))) (F₁-η h) ◃∙
      ap (G₁ ∘ D.comp (F₁ (G₁ f))) (! (F.pres-comp (G₁ g) (G₁ h))) ◃∙
      ap G₁ (! (F.pres-comp (G₁ f) (C.comp (G₁ g) (G₁ h)))) ◃∙
      G₁-β (C.comp (G₁ f) (C.comp (G₁ g) (G₁ h))) ◃∎
        =ₛ⟨ 1 & 3 & step₁₂ ⟩
      ap G₁ (D.assoc f g h) ◃∙
      ap2 (λ s t → G₁ (D.comp s t)) (F₁-η f) (F₁-η (D.comp g h)) ◃∙
      ap (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁) (ap2 (λ s t → G₁ (D.comp s t)) (F₁-η g) (F₁-η h)) ◃∙
      ap (G₁ ∘ D.comp (F₁ (G₁ f))) (F₁-β (D.comp (F₁ (G₁ g)) (F₁ (G₁ h)))) ◃∙
      ap (G₁ ∘ D.comp (F₁ (G₁ f))) (! (F.pres-comp (G₁ g) (G₁ h))) ◃∙
      ap G₁ (! (F.pres-comp (G₁ f) (C.comp (G₁ g) (G₁ h)))) ◃∙
      G₁-β (C.comp (G₁ f) (C.comp (G₁ g) (G₁ h))) ◃∎
        =ₛ⟨ 3 & 2 & !ₛ $
            homotopy-naturality
              (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁ ∘ G₁)
              (G₁ ∘ D.comp (F₁ (G₁ f)))
              (ap (G₁ ∘ D.comp (F₁ (G₁ f))) ∘ F₁-β)
              (! (F.pres-comp (G₁ g) (G₁ h))) ⟩
      ap G₁ (D.assoc f g h) ◃∙
      ap2 (λ s t → G₁ (D.comp s t)) (F₁-η f) (F₁-η (D.comp g h)) ◃∙
      ap (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁) (ap2 (λ s t → G₁ (D.comp s t)) (F₁-η g) (F₁-η h)) ◃∙
      ap (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁ ∘ G₁) (! (F.pres-comp (G₁ g) (G₁ h))) ◃∙
      ap (G₁ ∘ D.comp (F₁ (G₁ f))) (F₁-β (F₁ (C.comp (G₁ g) (G₁ h)))) ◃∙
      ap G₁ (! (F.pres-comp (G₁ f) (C.comp (G₁ g) (G₁ h)))) ◃∙
      G₁-β (C.comp (G₁ f) (C.comp (G₁ g) (G₁ h))) ◃∎
        =ₛ₁⟨ 3 & 1 & ap-∘ (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁) G₁ (! (F.pres-comp (G₁ g) (G₁ h))) ⟩
      ap G₁ (D.assoc f g h) ◃∙
      ap2 (λ s t → G₁ (D.comp s t)) (F₁-η f) (F₁-η (D.comp g h)) ◃∙
      ap (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁) (ap2 (λ s t → G₁ (D.comp s t)) (F₁-η g) (F₁-η h)) ◃∙
      ap (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁) (ap G₁ (! (F.pres-comp (G₁ g) (G₁ h)))) ◃∙
      ap (G₁ ∘ D.comp (F₁ (G₁ f))) (F₁-β (F₁ (C.comp (G₁ g) (G₁ h)))) ◃∙
      ap G₁ (! (F.pres-comp (G₁ f) (C.comp (G₁ g) (G₁ h)))) ◃∙
      G₁-β (C.comp (G₁ f) (C.comp (G₁ g) (G₁ h))) ◃∎
        =ₛ₁⟨ 4 & 1 &
             ! $ ap (ap (G₁ ∘ D.comp (F₁ (G₁ f)))) $
             F₁-is-equiv.adj (G₀ x) (G₀ z) (C.comp (G₁ g) (G₁ h)) ⟩
      ap G₁ (D.assoc f g h) ◃∙
      ap2 (λ s t → G₁ (D.comp s t)) (F₁-η f) (F₁-η (D.comp g h)) ◃∙
      ap (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁) (ap2 (λ s t → G₁ (D.comp s t)) (F₁-η g) (F₁-η h)) ◃∙
      ap (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁) (ap G₁ (! (F.pres-comp (G₁ g) (G₁ h)))) ◃∙
      ap (G₁ ∘ D.comp (F₁ (G₁ f))) (ap F₁ (G₁-β (C.comp (G₁ g) (G₁ h)))) ◃∙
      ap G₁ (! (F.pres-comp (G₁ f) (C.comp (G₁ g) (G₁ h)))) ◃∙
      G₁-β (C.comp (G₁ f) (C.comp (G₁ g) (G₁ h))) ◃∎
        =ₛ₁⟨ 4 & 1 & ∘-ap (G₁ ∘ D.comp (F₁ (G₁ f))) F₁ (G₁-β (C.comp (G₁ g) (G₁ h))) ⟩
      ap G₁ (D.assoc f g h) ◃∙
      ap2 (λ s t → G₁ (D.comp s t)) (F₁-η f) (F₁-η (D.comp g h)) ◃∙
      ap (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁) (ap2 (λ s t → G₁ (D.comp s t)) (F₁-η g) (F₁-η h)) ◃∙
      ap (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁) (ap G₁ (! (F.pres-comp (G₁ g) (G₁ h)))) ◃∙
      ap (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁) (G₁-β (C.comp (G₁ g) (G₁ h))) ◃∙
      ap G₁ (! (F.pres-comp (G₁ f) (C.comp (G₁ g) (G₁ h)))) ◃∙
      G₁-β (C.comp (G₁ f) (C.comp (G₁ g) (G₁ h))) ◃∎
        =ₛ⟨ 2 & 3 & ap-seq-=ₛ (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁) (!ₛ (G₁-pres-comp-β g h)) ⟩
      ap G₁ (D.assoc f g h) ◃∙
      ap2 (λ s t → G₁ (D.comp s t)) (F₁-η f) (F₁-η (D.comp g h)) ◃∙
      ap (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁) (G₁-pres-comp g h) ◃∙
      ap G₁ (! (F.pres-comp (G₁ f) (C.comp (G₁ g) (G₁ h)))) ◃∙
      G₁-β (C.comp (G₁ f) (C.comp (G₁ g) (G₁ h))) ◃∎
        =ₛ⟨ 2 & 2 &
            homotopy-naturality
              (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁)
              (G₁ ∘ F₁ ∘ C.comp (G₁ f))
              (λ s → ap G₁ (! (F.pres-comp (G₁ f) s)))
              (G₁-pres-comp g h) ⟩
      ap G₁ (D.assoc f g h) ◃∙
      ap2 (λ s t → G₁ (D.comp s t)) (F₁-η f) (F₁-η (D.comp g h)) ◃∙
      ap G₁ (! (F.pres-comp (G₁ f) (G₁ (D.comp g h)))) ◃∙
      ap (G₁ ∘ F₁ ∘ C.comp (G₁ f)) (G₁-pres-comp g h) ◃∙
      G₁-β (C.comp (G₁ f) (C.comp (G₁ g) (G₁ h))) ◃∎
        =ₛ⟨ 3 & 2 &
            homotopy-naturality
              (G₁ ∘ F₁ ∘ C.comp (G₁ f))
              (C.comp (G₁ f))
              (G₁-β ∘ C.comp (G₁ f))
              (G₁-pres-comp g h) ⟩
      ap G₁ (D.assoc f g h) ◃∙
      ap2 (λ s t → G₁ (D.comp s t)) (F₁-η f) (F₁-η (D.comp g h)) ◃∙
      ap G₁ (! (F.pres-comp (G₁ f) (G₁ (D.comp g h)))) ◃∙
      G₁-β (C.comp (G₁ f) (G₁ (D.comp g h))) ◃∙
      ap (C.comp (G₁ f)) (G₁-pres-comp g h) ◃∎
        =ₛ⟨ 1 & 3 & !ₛ (G₁-pres-comp-β f (D.comp g h)) ⟩
      ap G₁ (D.assoc f g h) ◃∙
      G₁-pres-comp f (D.comp g h) ◃∙
      ap (C.comp (G₁ f)) (G₁-pres-comp g h) ◃∎ ∎ₛ
      where
        step₅ : ap (λ s → G₁ (D.comp (F₁ s) (F₁ (G₁ h)))) (G₁-β (C.comp (G₁ f) (G₁ g)))
                ==
                ap (λ s → G₁ (D.comp s (F₁ (G₁ h)))) (F₁-β (F₁ (C.comp (G₁ f) (G₁ g))))
        step₅ =
          ap (λ s → G₁ (D.comp (F₁ s) (F₁ (G₁ h)))) (G₁-β (C.comp (G₁ f) (G₁ g)))
            =⟨ ap-∘ (λ s → G₁ (D.comp s (F₁ (G₁ h)))) F₁ (G₁-β (C.comp (G₁ f) (G₁ g))) ⟩
          ap (λ s → G₁ (D.comp s (F₁ (G₁ h)))) (ap F₁ (G₁-β (C.comp (G₁ f) (G₁ g))))
            =⟨ ap (ap (λ s → G₁ (D.comp s (F₁ (G₁ h)))))
                  (F₁-is-equiv.adj (G₀ w) (G₀ y) (C.comp (G₁ f) (G₁ g))) ⟩
          ap (λ s → G₁ (D.comp s (F₁ (G₁ h)))) (F₁-β (F₁ (C.comp (G₁ f) (G₁ g)))) =∎
        step₈ : ap2 (λ s t → G₁ (D.comp s t)) (F₁-η (D.comp f g)) (F₁-η h) ◃∙
                ap (λ s → G₁ (D.comp (F₁ s) (F₁ (G₁ h)))) (ap2 (λ s t → G₁ (D.comp s t)) (F₁-η f) (F₁-η g)) ◃∙
                ap (λ s → G₁ (D.comp s (F₁ (G₁ h)))) (F₁-β (D.comp (F₁ (G₁ f)) (F₁ (G₁ g)))) ◃∎
                =ₛ
                ap (λ s → G₁ (D.comp (D.comp s g) h)) (F₁-η f) ◃∙
                ap (λ s → G₁ (D.comp (D.comp (F₁ (G₁ f)) s) h)) (F₁-η g) ◃∙
                ap (λ s → G₁ (D.comp (D.comp (F₁ (G₁ f)) (F₁ (G₁ g))) s)) (F₁-η h) ◃∎
        step₈ =
          ap2 (λ s t → G₁ (D.comp s t)) (F₁-η (D.comp f g)) (F₁-η h) ◃∙
          ap (λ s → G₁ (D.comp (F₁ s) (F₁ (G₁ h)))) (ap2 (λ s t → G₁ (D.comp s t)) (F₁-η f) (F₁-η g)) ◃∙
          ap (λ s → G₁ (D.comp s (F₁ (G₁ h)))) (F₁-β (D.comp (F₁ (G₁ f)) (F₁ (G₁ g)))) ◃∎
            =ₛ₁⟨ 1 & 1 & ap (ap (λ s → G₁ (D.comp (F₁ s) (F₁ (G₁ h)))))
                            (! (ap-ap2 G₁ D.comp (F₁-η f) (F₁-η g))) ⟩
          ap2 (λ s t → G₁ (D.comp s t)) (F₁-η (D.comp f g)) (F₁-η h) ◃∙
          ap (λ s → G₁ (D.comp (F₁ s) (F₁ (G₁ h)))) (ap G₁ (ap2 D.comp (F₁-η f) (F₁-η g))) ◃∙
          ap (λ s → G₁ (D.comp s (F₁ (G₁ h)))) (F₁-β (D.comp (F₁ (G₁ f)) (F₁ (G₁ g)))) ◃∎
            =ₛ₁⟨ 1 & 1 & ∘-ap (λ s → G₁ (D.comp (F₁ s) (F₁ (G₁ h)))) G₁ (ap2 D.comp (F₁-η f) (F₁-η g)) ⟩
          ap2 (λ s t → G₁ (D.comp s t)) (F₁-η (D.comp f g)) (F₁-η h) ◃∙
          ap (λ s → G₁ (D.comp (F₁ (G₁ s)) (F₁ (G₁ h)))) (ap2 D.comp (F₁-η f) (F₁-η g)) ◃∙
          ap (λ s → G₁ (D.comp s (F₁ (G₁ h)))) (F₁-β (D.comp (F₁ (G₁ f)) (F₁ (G₁ g)))) ◃∎
            =ₛ⟨ 0 & 2 & !ₛ $
                homotopy-naturality (λ s → G₁ (D.comp s h))
                                    (λ s → G₁ (D.comp (F₁ (G₁ s)) (F₁ (G₁ h))))
                                    (λ s → ap2 (λ s t → G₁ (D.comp s t)) (F₁-η s) (F₁-η h))
                                    (ap2 D.comp (F₁-η f) (F₁-η g)) ⟩
          ap (λ s → G₁ (D.comp s h)) (ap2 D.comp (F₁-η f) (F₁-η g)) ◃∙
          ap2 (λ s t → G₁ (D.comp s t)) (F₁-η (D.comp (F₁ (G₁ f)) (F₁ (G₁ g)))) (F₁-η h) ◃∙
          ap (λ s → G₁ (D.comp s (F₁ (G₁ h)))) (F₁-β (D.comp (F₁ (G₁ f)) (F₁ (G₁ g)))) ◃∎
            =ₛ⟨ 1 & 1 & ap2-out' (λ s t → G₁ (D.comp s t)) (F₁-η (D.comp (F₁ (G₁ f)) (F₁ (G₁ g)))) (F₁-η h) ⟩
          ap (λ s → G₁ (D.comp s h)) (ap2 D.comp (F₁-η f) (F₁-η g)) ◃∙
          ap (λ t → G₁ (D.comp (D.comp (F₁ (G₁ f)) (F₁ (G₁ g))) t)) (F₁-η h) ◃∙
          ap (λ s → G₁ (D.comp s (F₁ (G₁ h)))) (F₁-η (D.comp (F₁ (G₁ f)) (F₁ (G₁ g)))) ◃∙
          ap (λ s → G₁ (D.comp s (F₁ (G₁ h)))) (F₁-β (D.comp (F₁ (G₁ f)) (F₁ (G₁ g)))) ◃∎
            =ₛ⟨ 2 & 2 &
                ap-seq-=ₛ (λ s → G₁ (D.comp s (F₁ (G₁ h)))) $
                =ₛ-in {s = F₁-η (D.comp (F₁ (G₁ f)) (F₁ (G₁ g))) ◃∙
                           F₁-β (D.comp (F₁ (G₁ f)) (F₁ (G₁ g))) ◃∎}
                      {t = D.comp (F₁ (G₁ f)) (F₁ (G₁ g)) ∎∎}
                      (!-inv-l (F₁-β (D.comp (F₁ (G₁ f)) (F₁ (G₁ g))))) ⟩
          ap (λ s → G₁ (D.comp s h)) (ap2 D.comp (F₁-η f) (F₁-η g)) ◃∙
          ap (λ t → G₁ (D.comp (D.comp (F₁ (G₁ f)) (F₁ (G₁ g))) t)) (F₁-η h) ◃∎
            =ₛ₁⟨ 0 & 1 & ap-ap2 (λ s → G₁ (D.comp s h)) D.comp (F₁-η f) (F₁-η g) ⟩
          ap2 (λ s t → G₁ (D.comp (D.comp s t) h)) (F₁-η f) (F₁-η g) ◃∙
          ap (λ t → G₁ (D.comp (D.comp (F₁ (G₁ f)) (F₁ (G₁ g))) t)) (F₁-η h) ◃∎
            =ₛ⟨ 0 & 1 & ap2-out (λ s t → G₁ (D.comp (D.comp s t) h)) (F₁-η f) (F₁-η g) ⟩
          ap (λ s → G₁ (D.comp (D.comp s g) h)) (F₁-η f) ◃∙
          ap (λ s → G₁ (D.comp (D.comp (F₁ (G₁ f)) s) h)) (F₁-η g) ◃∙
          ap (λ s → G₁ (D.comp (D.comp (F₁ (G₁ f)) (F₁ (G₁ g))) s)) (F₁-η h) ◃∎ ∎ₛ
        step₁₀' : ap (λ s → D.comp s (F₁ (G₁ h))) (! (F.pres-comp (G₁ f) (G₁ g))) ◃∙
                  ! (F.pres-comp (C.comp (G₁ f) (G₁ g)) (G₁ h)) ◃∙
                  ap F₁ (C.assoc (G₁ f) (G₁ g) (G₁ h)) ◃∎
                  =ₛ
                  D.assoc (F₁ (G₁ f)) (F₁ (G₁ g)) (F₁ (G₁ h)) ◃∙
                  ap (D.comp (F₁ (G₁ f))) (! (F.pres-comp (G₁ g) (G₁ h))) ◃∙
                  ! (F.pres-comp (G₁ f) (C.comp (G₁ g) (G₁ h))) ◃∎
        step₁₀' =
          ap (λ s → D.comp s (F₁ (G₁ h))) (! (F.pres-comp (G₁ f) (G₁ g))) ◃∙
          ! e₀₋₁ ◃∙
          e₀₋₄ ◃∎
            =ₛ₁⟨ 0 & 1 & ap-! (λ s → D.comp s (F₁ (G₁ h))) (F.pres-comp (G₁ f) (G₁ g)) ⟩
          ! e₁₋₂ ◃∙ ! e₀₋₁ ◃∙ e₀₋₄ ◃∎
            =ₛ⟨ post-rotate-seq-in {p = ! e₁₋₂ ◃∙ ! e₀₋₁ ◃∙ e₀₋₄ ◃∎} $
                pre-rotate'-seq-in {p = e₀₋₁ ◃∙ e₁₋₂ ◃∎} $
                !ₛ $ F.pres-comp-coh (G₁ f) (G₁ g) (G₁ h) ⟩
          e₂₋₃ ◃∙ ! e₅₋₃ ◃∙ ! e₄₋₅ ◃∎
            =ₛ₁⟨ 1 & 1 & !-ap (D.comp (F₁ (G₁ f))) (F.pres-comp (G₁ g) (G₁ h)) ⟩
          e₂₋₃ ◃∙
          ap (D.comp (F₁ (G₁ f))) (! (F.pres-comp (G₁ g) (G₁ h))) ◃∙
          ! e₄₋₅ ◃∎ ∎ₛ
          where
            t₀ : D.Arr (F₀ (G₀ w)) (F₀ (G₀ z))
            t₀ = F₁ (C.comp (C.comp (G₁ f) (G₁ g)) (G₁ h))
            t₁ : D.Arr (F₀ (G₀ w)) (F₀ (G₀ z))
            t₁ = D.comp (F₁ (C.comp (G₁ f) (G₁ g))) (F₁ (G₁ h))
            t₂ : D.Arr (F₀ (G₀ w)) (F₀ (G₀ z))
            t₂ = D.comp (D.comp (F₁ (G₁ f)) (F₁ (G₁ g))) (F₁ (G₁ h))
            t₃ : D.Arr (F₀ (G₀ w)) (F₀ (G₀ z))
            t₃ = D.comp (F₁ (G₁ f)) (D.comp (F₁ (G₁ g)) (F₁ (G₁ h)))
            t₄ : D.Arr (F₀ (G₀ w)) (F₀ (G₀ z))
            t₄ = F₁ (C.comp (G₁ f) (C.comp (G₁ g) (G₁ h)))
            t₅ = D.comp (F₁ (G₁ f)) (F₁ (C.comp (G₁ g) (G₁ h)))
            e₀₋₁ : t₀ == t₁
            e₀₋₁ = F.pres-comp (C.comp (G₁ f) (G₁ g)) (G₁ h)
            e₁₋₂ : t₁ == t₂
            e₁₋₂ = ap (λ s → D.comp s (F₁ (G₁ h))) (F.pres-comp (G₁ f) (G₁ g))
            e₂₋₃ : t₂ == t₃
            e₂₋₃ = D.assoc (F₁ (G₁ f)) (F₁ (G₁ g)) (F₁ (G₁ h))
            e₀₋₄ : t₀ == t₄
            e₀₋₄ = ap F₁ (C.assoc (G₁ f) (G₁ g) (G₁ h))
            e₄₋₅ : t₄ == t₅
            e₄₋₅ = F.pres-comp (G₁ f) (C.comp (G₁ g) (G₁ h))
            e₅₋₃ : t₅ == t₃
            e₅₋₃ = ap (D.comp (F₁ (G₁ f))) (F.pres-comp (G₁ g) (G₁ h))
        step₁₀ : ap (λ s → G₁ (D.comp s (F₁ (G₁ h)))) (! (F.pres-comp (G₁ f) (G₁ g))) ◃∙
                 ap G₁ (! (F.pres-comp (C.comp (G₁ f) (G₁ g)) (G₁ h))) ◃∙
                 ap (G₁ ∘ F₁) (C.assoc (G₁ f) (G₁ g) (G₁ h)) ◃∎
                 =ₛ
                 ap G₁ (D.assoc (F₁ (G₁ f)) (F₁ (G₁ g)) (F₁ (G₁ h))) ◃∙
                 ap (G₁ ∘ D.comp (F₁ (G₁ f))) (! (F.pres-comp (G₁ g) (G₁ h))) ◃∙
                 ap G₁ (! (F.pres-comp (G₁ f) (C.comp (G₁ g) (G₁ h)))) ◃∎
        step₁₀ =
          ap (λ s → G₁ (D.comp s (F₁ (G₁ h)))) (! (F.pres-comp (G₁ f) (G₁ g))) ◃∙
          ap G₁ (! (F.pres-comp (C.comp (G₁ f) (G₁ g)) (G₁ h))) ◃∙
          ap (G₁ ∘ F₁) (C.assoc (G₁ f) (G₁ g) (G₁ h)) ◃∎
            =ₛ₁⟨ 0 & 1 & ap-∘ G₁ (λ s → D.comp s (F₁ (G₁ h))) (! (F.pres-comp (G₁ f) (G₁ g))) ⟩
          ap G₁ (ap (λ s → D.comp s (F₁ (G₁ h))) (! (F.pres-comp (G₁ f) (G₁ g)))) ◃∙
          ap G₁ (! (F.pres-comp (C.comp (G₁ f) (G₁ g)) (G₁ h))) ◃∙
          ap (G₁ ∘ F₁) (C.assoc (G₁ f) (G₁ g) (G₁ h)) ◃∎
            =ₛ₁⟨ 2 & 1 & ap-∘ G₁ F₁ (C.assoc (G₁ f) (G₁ g) (G₁ h)) ⟩
          ap G₁ (ap (λ s → D.comp s (F₁ (G₁ h))) (! (F.pres-comp (G₁ f) (G₁ g)))) ◃∙
          ap G₁ (! (F.pres-comp (C.comp (G₁ f) (G₁ g)) (G₁ h))) ◃∙
          ap G₁ (ap F₁ (C.assoc (G₁ f) (G₁ g) (G₁ h))) ◃∎
            =ₛ⟨ ap-seq-=ₛ G₁ step₁₀' ⟩
          ap G₁ (D.assoc (F₁ (G₁ f)) (F₁ (G₁ g)) (F₁ (G₁ h))) ◃∙
          ap G₁ (ap (D.comp (F₁ (G₁ f))) (! (F.pres-comp (G₁ g) (G₁ h)))) ◃∙
          ap G₁ (! (F.pres-comp (G₁ f) (C.comp (G₁ g) (G₁ h)))) ◃∎
            =ₛ₁⟨ 1 & 1 & ∘-ap G₁ (D.comp (F₁ (G₁ f))) (! (F.pres-comp (G₁ g) (G₁ h))) ⟩
          ap G₁ (D.assoc (F₁ (G₁ f)) (F₁ (G₁ g)) (F₁ (G₁ h))) ◃∙
          ap (G₁ ∘ D.comp (F₁ (G₁ f))) (! (F.pres-comp (G₁ g) (G₁ h))) ◃∙
          ap G₁ (! (F.pres-comp (G₁ f) (C.comp (G₁ g) (G₁ h)))) ◃∎ ∎ₛ
        step₁₁ :
          ap (λ s → G₁ (D.comp (D.comp s g) h)) (F₁-η f) ◃∙
          ap (λ s → G₁ (D.comp (D.comp (F₁ (G₁ f)) s) h)) (F₁-η g) ◃∙
          ap (λ s → G₁ (D.comp (D.comp (F₁ (G₁ f)) (F₁ (G₁ g))) s)) (F₁-η h) ◃∙
          ap G₁ (D.assoc (F₁ (G₁ f)) (F₁ (G₁ g)) (F₁ (G₁ h))) ◃∎
          =ₛ
          ap G₁ (D.assoc f g h) ◃∙
          ap (λ s → G₁ (D.comp s (D.comp g h))) (F₁-η f) ◃∙
          ap (λ s → G₁ (D.comp (F₁ (G₁ f)) (D.comp s h))) (F₁-η g) ◃∙
          ap (λ s → G₁ (D.comp (F₁ (G₁ f)) (D.comp (F₁ (G₁ g)) s))) (F₁-η h) ◃∎
        step₁₁ =
          ap (λ s → G₁ (D.comp (D.comp s g) h)) (F₁-η f) ◃∙
          ap (λ s → G₁ (D.comp (D.comp (F₁ (G₁ f)) s) h)) (F₁-η g) ◃∙
          ap (λ s → G₁ (D.comp (D.comp (F₁ (G₁ f)) (F₁ (G₁ g))) s)) (F₁-η h) ◃∙
          ap G₁ (D.assoc (F₁ (G₁ f)) (F₁ (G₁ g)) (F₁ (G₁ h))) ◃∎
            =ₛ⟨ 2 & 2 &
                homotopy-naturality (λ s → G₁ (D.comp (D.comp (F₁ (G₁ f)) (F₁ (G₁ g))) s))
                                    (λ s → G₁ (D.comp (F₁ (G₁ f)) (D.comp (F₁ (G₁ g)) s)))
                                    (λ s → ap G₁ (D.assoc (F₁ (G₁ f)) (F₁ (G₁ g)) s))
                                    (F₁-η h) ⟩
          ap (λ s → G₁ (D.comp (D.comp s g) h)) (F₁-η f) ◃∙
          ap (λ s → G₁ (D.comp (D.comp (F₁ (G₁ f)) s) h)) (F₁-η g) ◃∙
          ap G₁ (D.assoc (F₁ (G₁ f)) (F₁ (G₁ g)) h) ◃∙
          ap (λ s → G₁ (D.comp (F₁ (G₁ f)) (D.comp (F₁ (G₁ g)) s))) (F₁-η h) ◃∎
            =ₛ⟨ 1 & 2 &
                homotopy-naturality (λ s → G₁ (D.comp (D.comp (F₁ (G₁ f)) s) h))
                                    (λ s → G₁ (D.comp (F₁ (G₁ f)) (D.comp s h)))
                                    (λ s → ap G₁ (D.assoc (F₁ (G₁ f)) s h))
                                    (F₁-η g) ⟩
          ap (λ s → G₁ (D.comp (D.comp s g) h)) (F₁-η f) ◃∙
          ap G₁ (D.assoc (F₁ (G₁ f)) g h) ◃∙
          ap (λ s → G₁ (D.comp (F₁ (G₁ f)) (D.comp s h))) (F₁-η g) ◃∙
          ap (λ s → G₁ (D.comp (F₁ (G₁ f)) (D.comp (F₁ (G₁ g)) s))) (F₁-η h) ◃∎
            =ₛ⟨ 0 & 2 &
                homotopy-naturality (λ s → G₁ (D.comp (D.comp s g) h))
                                    (λ s → G₁ (D.comp s (D.comp g h)))
                                    (λ s → ap G₁ (D.assoc s g h))
                                    (F₁-η f) ⟩
          ap G₁ (D.assoc f g h) ◃∙
          ap (λ s → G₁ (D.comp s (D.comp g h))) (F₁-η f) ◃∙
          ap (λ s → G₁ (D.comp (F₁ (G₁ f)) (D.comp s h))) (F₁-η g) ◃∙
          ap (λ s → G₁ (D.comp (F₁ (G₁ f)) (D.comp (F₁ (G₁ g)) s))) (F₁-η h) ◃∎ ∎ₛ
        step₁₂ : ap (λ s → G₁ (D.comp s (D.comp g h))) (F₁-η f) ◃∙
                 ap (λ s → G₁ (D.comp (F₁ (G₁ f)) (D.comp s h))) (F₁-η g) ◃∙
                 ap (λ s → G₁ (D.comp (F₁ (G₁ f)) (D.comp (F₁ (G₁ g)) s))) (F₁-η h) ◃∎
                 =ₛ
                 ap2 (λ s t → G₁ (D.comp s t)) (F₁-η f) (F₁-η (D.comp g h)) ◃∙
                 ap (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁) (ap2 (λ s t → G₁ (D.comp s t)) (F₁-η g) (F₁-η h)) ◃∙
                 ap (G₁ ∘ D.comp (F₁ (G₁ f))) (F₁-β (D.comp (F₁ (G₁ g)) (F₁ (G₁ h)))) ◃∎
        step₁₂ =
          ap (λ s → G₁ (D.comp s (D.comp g h))) (F₁-η f) ◃∙
          ap (λ s → G₁ (D.comp (F₁ (G₁ f)) (D.comp s h))) (F₁-η g) ◃∙
          ap (λ s → G₁ (D.comp (F₁ (G₁ f)) (D.comp (F₁ (G₁ g)) s))) (F₁-η h) ◃∎
            =ₛ⟨ 1 & 2 & !ₛ (ap2-out (λ s t → G₁ (D.comp (F₁ (G₁ f)) (D.comp s t))) (F₁-η g) (F₁-η h)) ⟩
          ap (λ s → G₁ (D.comp s (D.comp g h))) (F₁-η f) ◃∙
          ap2 (λ s t → G₁ (D.comp (F₁ (G₁ f)) (D.comp s t))) (F₁-η g) (F₁-η h) ◃∎
            =ₛ₁⟨ 1 & 1 & ! (ap-ap2 (G₁ ∘ D.comp (F₁ (G₁ f))) D.comp (F₁-η g) (F₁-η h)) ⟩
          ap (λ s → G₁ (D.comp s (D.comp g h))) (F₁-η f) ◃∙
          ap (G₁ ∘ D.comp (F₁ (G₁ f))) (ap2 D.comp (F₁-η g) (F₁-η h)) ◃∎
            =ₛ⟨ 2 & 0 &
                 ap-seq-=ₛ (G₁ ∘ D.comp (F₁ (G₁ f))) $
                 =ₛ-in {s = D.comp (F₁ (G₁ g)) (F₁ (G₁ h)) ∎∎}
                       {t = F₁-η (D.comp (F₁ (G₁ g)) (F₁ (G₁ h))) ◃∙
                            F₁-β (D.comp (F₁ (G₁ g)) (F₁ (G₁ h))) ◃∎}
                       (! (!-inv-l (F₁-β (D.comp (F₁ (G₁ g)) (F₁ (G₁ h)))))) ⟩
          ap (λ s → G₁ (D.comp s (D.comp g h))) (F₁-η f) ◃∙
          ap (G₁ ∘ D.comp (F₁ (G₁ f))) (ap2 D.comp (F₁-η g) (F₁-η h)) ◃∙
          ap (G₁ ∘ D.comp (F₁ (G₁ f))) (F₁-η (D.comp (F₁ (G₁ g)) (F₁ (G₁ h)))) ◃∙
          ap (G₁ ∘ D.comp (F₁ (G₁ f))) (F₁-β (D.comp (F₁ (G₁ g)) (F₁ (G₁ h)))) ◃∎
            =ₛ⟨ 1 & 2 &
                homotopy-naturality (G₁ ∘ D.comp (F₁ (G₁ f)))
                                    (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁ ∘ G₁)
                                    (ap (G₁ ∘ D.comp (F₁ (G₁ f))) ∘ F₁-η)
                                    (ap2 D.comp (F₁-η g) (F₁-η h)) ⟩
          ap (λ s → G₁ (D.comp s (D.comp g h))) (F₁-η f) ◃∙
          ap (G₁ ∘ D.comp (F₁ (G₁ f))) (F₁-η (D.comp g h)) ◃∙
          ap (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁ ∘ G₁) (ap2 D.comp (F₁-η g) (F₁-η h)) ◃∙
          ap (G₁ ∘ D.comp (F₁ (G₁ f))) (F₁-β (D.comp (F₁ (G₁ g)) (F₁ (G₁ h)))) ◃∎
            =ₛ⟨ 0 & 2 & !ₛ (ap2-out (λ s t → G₁ (D.comp s t)) (F₁-η f) (F₁-η (D.comp g h))) ⟩
          ap2 (λ s t → G₁ (D.comp s t)) (F₁-η f) (F₁-η (D.comp g h)) ◃∙
          ap (λ s → G₁ (D.comp (F₁ (G₁ f)) (F₁ (G₁ s)))) (ap2 D.comp (F₁-η g) (F₁-η h)) ◃∙
          ap (G₁ ∘ D.comp (F₁ (G₁ f))) (F₁-β (D.comp (F₁ (G₁ g)) (F₁ (G₁ h)))) ◃∎
            =ₛ₁⟨ 1 & 1 & ap-ap2 (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁ ∘ G₁) D.comp (F₁-η g) (F₁-η h) ⟩
          ap2 (λ s t → G₁ (D.comp s t)) (F₁-η f) (F₁-η (D.comp g h)) ◃∙
          ap2 (λ s t → G₁ (D.comp (F₁ (G₁ f)) (F₁ (G₁ (D.comp s t))))) (F₁-η g) (F₁-η h) ◃∙
          ap (G₁ ∘ D.comp (F₁ (G₁ f))) (F₁-β (D.comp (F₁ (G₁ g)) (F₁ (G₁ h)))) ◃∎
            =ₛ₁⟨ 1 & 1 &
                 ! (ap-ap2 (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁)
                           (λ s t → G₁ (D.comp s t))
                           (F₁-η g)
                           (F₁-η h)) ⟩
          ap2 (λ s t → G₁ (D.comp s t)) (F₁-η f) (F₁-η (D.comp g h)) ◃∙
          ap (G₁ ∘ D.comp (F₁ (G₁ f)) ∘ F₁) (ap2 (λ s t → G₁ (D.comp s t)) (F₁-η g) (F₁-η h)) ◃∙
          ap (G₁ ∘ D.comp (F₁ (G₁ f))) (F₁-β (D.comp (F₁ (G₁ g)) (F₁ (G₁ h)))) ◃∎ ∎ₛ

    G : TwoSemiFunctor D' C
    G =
      record
      { F₀ = G₀
      ; F₁ = G₁
      ; pres-comp = G₁-pres-comp
      ; pres-comp-coh = G₁-pres-comp-coh
      }

    module G = TwoSemiFunctor G

  module Comp = FunctorComposition N G
  open Comp using () renaming (composition to functor) public
  open TwoSemiFunctor functor public

  abstract
    pres-comp-β : {x y z : D.El} (f : D.Arr x y) (g : D.Arr y z)
      → pres-comp f g ◃∎
        =ₛ
        ap G.F₁ (N.pres-comp f g) ◃∙
        G₁-pres-comp-seq (N.F₁ f) (N.F₁ g)
    pres-comp-β f g =
      pres-comp f g ◃∎
        =ₛ⟨ Comp.pres-comp-β f g ⟩
      ap G.F₁ (N.pres-comp f g) ◃∙
      G₁-pres-comp (N.F₁ f) (N.F₁ g) ◃∎
        =ₛ⟨ 1 & 1 & G₁-pres-comp-β (N.F₁ f) (N.F₁ g) ⟩
      ap G.F₁ (N.pres-comp f g) ◃∙
      G₁-pres-comp-seq (N.F₁ f) (N.F₁ g) ∎ₛ

open FunctorInverse
  using ()
  renaming (functor to functor-inverse) public
