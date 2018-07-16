{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Paths
open import lib.types.TwoSemiCategory

module lib.two-semi-categories.Functor where

record TwoSemiFunctor {i₁ j₁ i₂ j₂} (C : TwoSemiCategory i₁ j₁) (D : TwoSemiCategory i₂ j₂)
  : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
  private
    module C = TwoSemiCategory C
    module D = TwoSemiCategory D
  field
    F₀ : C.El → D.El
    F₁ : {x y : C.El} → C.Arr x y → D.Arr (F₀ x) (F₀ y)
    pres-comp : {x y z : C.El} (f : C.Arr x y) (g : C.Arr y z)
      → F₁ (C.comp f g) == D.comp (F₁ f) (F₁ g)

  pres-comp-coh-seq₁ : {w x y z : C.El} (f : C.Arr w x) (g : C.Arr x y) (h : C.Arr y z)
    → F₁ (C.comp (C.comp f g) h) =-= D.comp (F₁ f) (D.comp (F₁ g) (F₁ h))
  pres-comp-coh-seq₁ f g h =
    F₁ (C.comp (C.comp f g) h)
      =⟪ pres-comp (C.comp f g) h ⟫
    D.comp (F₁ (C.comp f g)) (F₁ h)
      =⟪ ap (λ s → D.comp s (F₁ h)) (pres-comp f g) ⟫
    D.comp (D.comp (F₁ f) (F₁ g)) (F₁ h)
      =⟪ D.assoc (F₁ f) (F₁ g) (F₁ h) ⟫
    D.comp (F₁ f) (D.comp (F₁ g) (F₁ h)) ∎∎

  pres-comp-coh-seq₂ : {w x y z : C.El} (f : C.Arr w x) (g : C.Arr x y) (h : C.Arr y z)
    → F₁ (C.comp (C.comp f g) h) =-= D.comp (F₁ f) (D.comp (F₁ g) (F₁ h))
  pres-comp-coh-seq₂ f g h =
    F₁ (C.comp (C.comp f g) h)
      =⟪ ap F₁ (C.assoc f g h) ⟫
    F₁ (C.comp f (C.comp g h))
      =⟪ pres-comp f (C.comp g h) ⟫
    D.comp (F₁ f) (F₁ (C.comp g h))
      =⟪ ap (D.comp (F₁ f)) (pres-comp g h) ⟫
    D.comp (F₁ f) (D.comp (F₁ g) (F₁ h)) ∎∎

  field
    pres-comp-coh : {w x y z : C.El} (f : C.Arr w x) (g : C.Arr x y) (h : C.Arr y z)
      → pres-comp-coh-seq₁ f g h =ₛ pres-comp-coh-seq₂ f g h

module FunctorComposition
  {i₁ j₁ i₂ j₂ i₃ j₃} {C : TwoSemiCategory i₁ j₁} {D : TwoSemiCategory i₂ j₂} {E : TwoSemiCategory i₃ j₃}
  (F : TwoSemiFunctor C D) (G : TwoSemiFunctor D E) where

  private
    module C = TwoSemiCategory C
    module D = TwoSemiCategory D
    module E = TwoSemiCategory E
    module F = TwoSemiFunctor F
    module G = TwoSemiFunctor G

    F₀ : C.El → E.El
    F₀ = G.F₀ ∘ F.F₀

    F₁ : {x y : C.El} → C.Arr x y → E.Arr (F₀ x) (F₀ y)
    F₁ f = G.F₁ (F.F₁ f)

  pres-comp-seq : {x y z : C.El} (f : C.Arr x y) (g : C.Arr y z)
    → G.F₁ (F.F₁ (C.comp f g)) =-= E.comp (G.F₁ (F.F₁ f)) (G.F₁ (F.F₁ g))
  pres-comp-seq f g =
    G.F₁ (F.F₁ (C.comp f g))
      =⟪ ap G.F₁ (F.pres-comp f g) ⟫
    G.F₁ (D.comp (F.F₁ f) (F.F₁ g))
      =⟪ G.pres-comp (F.F₁ f) (F.F₁ g) ⟫
    E.comp (G.F₁ (F.F₁ f)) (G.F₁ (F.F₁ g)) ∎∎

  abstract
    pres-comp : {x y z : C.El} (f : C.Arr x y) (g : C.Arr y z)
      → G.F₁ (F.F₁ (C.comp f g)) == E.comp (G.F₁ (F.F₁ f)) (G.F₁ (F.F₁ g))
    pres-comp f g = ↯ (pres-comp-seq f g)

    pres-comp-β : {x y z : C.El} (f : C.Arr x y) (g : C.Arr y z)
      → pres-comp f g ◃∎ =ₛ pres-comp-seq f g
    pres-comp-β f g = =ₛ-in idp

  private
    abstract
      pres-comp-coh : {w x y z : C.El} (f : C.Arr w x) (g : C.Arr x y) (h : C.Arr y z)
        → pres-comp (C.comp f g) h ◃∙ ap (λ s → E.comp s (F₁ h)) (pres-comp f g) ◃∙ E.assoc (F₁ f) (F₁ g) (F₁ h) ◃∎
          =ₛ
          ap F₁ (C.assoc f g h) ◃∙ pres-comp f (C.comp g h) ◃∙ ap (E.comp (F₁ f)) (pres-comp g h) ◃∎
      pres-comp-coh f g h =
        pres-comp (C.comp f g) h ◃∙
        ap (λ s → E.comp s (F₁ h)) (pres-comp f g) ◃∙
        E.assoc (F₁ f) (F₁ g) (F₁ h) ◃∎
          =ₛ⟨ 0 & 1 & expand (pres-comp-seq (C.comp f g) h) ⟩
        ap G.F₁ (F.pres-comp (C.comp f g) h) ◃∙
        G.pres-comp (F.F₁ (C.comp f g)) (F.F₁ h) ◃∙
        ap (λ s → E.comp s (F₁ h)) (pres-comp f g) ◃∙
        E.assoc (F₁ f) (F₁ g) (F₁ h) ◃∎
          =ₛ⟨ 2 & 1 & ap-seq-∙ (λ s → E.comp s (F₁ h)) (pres-comp-seq f g) ⟩
        ap G.F₁ (F.pres-comp (C.comp f g) h) ◃∙
        G.pres-comp (F.F₁ (C.comp f g)) (F.F₁ h) ◃∙
        ap (λ s → E.comp s (F₁ h)) (ap G.F₁ (F.pres-comp f g)) ◃∙
        ap (λ s → E.comp s (F₁ h)) (G.pres-comp (F.F₁ f) (F.F₁ g)) ◃∙
        E.assoc (F₁ f) (F₁ g) (F₁ h) ◃∎
          =ₛ₁⟨ 2 & 1 & ∘-ap (λ s → E.comp s (F₁ h)) G.F₁ (F.pres-comp f g) ⟩
        ap G.F₁ (F.pres-comp (C.comp f g) h) ◃∙
        G.pres-comp (F.F₁ (C.comp f g)) (F.F₁ h) ◃∙
        ap (λ s → E.comp (G.F₁ s) (F₁ h)) (F.pres-comp f g) ◃∙
        ap (λ s → E.comp s (F₁ h)) (G.pres-comp (F.F₁ f) (F.F₁ g)) ◃∙
        E.assoc (F₁ f) (F₁ g) (F₁ h) ◃∎
          =ₛ⟨ 1 & 2 & !ₛ $
              homotopy-naturality (λ s → G.F₁ (D.comp s (F.F₁ h)))
                                  (λ s → E.comp (G.F₁ s) (F₁ h))
                                  (λ s → G.pres-comp s (F.F₁ h))
                                  (F.pres-comp f g) ⟩
        ap G.F₁ (F.pres-comp (C.comp f g) h) ◃∙
        ap (λ s → G.F₁ (D.comp s (F.F₁ h))) (F.pres-comp f g) ◃∙
        G.pres-comp (D.comp (F.F₁ f) (F.F₁ g)) (F.F₁ h) ◃∙
        ap (λ s → E.comp s (F₁ h)) (G.pres-comp (F.F₁ f) (F.F₁ g)) ◃∙
        E.assoc (F₁ f) (F₁ g) (F₁ h) ◃∎
          =ₛ⟨ 2 & 3 & G.pres-comp-coh (F.F₁ f) (F.F₁ g) (F.F₁ h) ⟩
        ap G.F₁ (F.pres-comp (C.comp f g) h) ◃∙
        ap (λ s → G.F₁ (D.comp s (F.F₁ h))) (F.pres-comp f g) ◃∙
        ap G.F₁ (D.assoc (F.F₁ f) (F.F₁ g) (F.F₁ h)) ◃∙
        G.pres-comp (F.F₁ f) (D.comp (F.F₁ g) (F.F₁ h)) ◃∙
        ap (E.comp (F₁ f)) (G.pres-comp (F.F₁ g) (F.F₁ h)) ◃∎
          =ₛ₁⟨ 1 & 1 & ap-∘ G.F₁ (λ s → D.comp s (F.F₁ h)) (F.pres-comp f g) ⟩
        ap G.F₁ (F.pres-comp (C.comp f g) h) ◃∙
        ap G.F₁ (ap (λ s → D.comp s (F.F₁ h)) (F.pres-comp f g)) ◃∙
        ap G.F₁ (D.assoc (F.F₁ f) (F.F₁ g) (F.F₁ h)) ◃∙
        G.pres-comp (F.F₁ f) (D.comp (F.F₁ g) (F.F₁ h)) ◃∙
        ap (E.comp (F₁ f)) (G.pres-comp (F.F₁ g) (F.F₁ h)) ◃∎
          =ₛ⟨ 0 & 3 & ap-seq-=ₛ G.F₁ (F.pres-comp-coh f g h) ⟩
        ap G.F₁ (ap F.F₁ (C.assoc f g h)) ◃∙
        ap G.F₁ (F.pres-comp f (C.comp g h)) ◃∙
        ap G.F₁ (ap (D.comp (F.F₁ f)) (F.pres-comp g h)) ◃∙
        G.pres-comp (F.F₁ f) (D.comp (F.F₁ g) (F.F₁ h)) ◃∙
        ap (E.comp (F₁ f)) (G.pres-comp (F.F₁ g) (F.F₁ h)) ◃∎
          =ₛ₁⟨ 2 & 1 & ∘-ap G.F₁ (D.comp (F.F₁ f)) (F.pres-comp g h) ⟩
        ap G.F₁ (ap F.F₁ (C.assoc f g h)) ◃∙
        ap G.F₁ (F.pres-comp f (C.comp g h)) ◃∙
        ap (G.F₁ ∘ D.comp (F.F₁ f)) (F.pres-comp g h) ◃∙
        G.pres-comp (F.F₁ f) (D.comp (F.F₁ g) (F.F₁ h)) ◃∙
        ap (E.comp (F₁ f)) (G.pres-comp (F.F₁ g) (F.F₁ h)) ◃∎
          =ₛ⟨ 2 & 2 &
              homotopy-naturality (G.F₁ ∘ D.comp (F.F₁ f))
                                  (E.comp (F₁ f) ∘ G.F₁)
                                  (G.pres-comp (F.F₁ f))
                                  (F.pres-comp g h) ⟩
        ap G.F₁ (ap F.F₁ (C.assoc f g h)) ◃∙
        ap G.F₁ (F.pres-comp f (C.comp g h)) ◃∙
        G.pres-comp (F.F₁ f) (F.F₁ (C.comp g h)) ◃∙
        ap (λ s → E.comp (F₁ f) (G.F₁ s)) (F.pres-comp g h) ◃∙
        ap (E.comp (F₁ f)) (G.pres-comp (F.F₁ g) (F.F₁ h)) ◃∎
          =ₛ⟨ 1 & 2 & contract ⟩
        ap G.F₁ (ap F.F₁ (C.assoc f g h)) ◃∙
        pres-comp f (C.comp g h) ◃∙
        ap (λ s → E.comp (F₁ f) (G.F₁ s)) (F.pres-comp g h) ◃∙
        ap (E.comp (F₁ f)) (G.pres-comp (F.F₁ g) (F.F₁ h)) ◃∎
          =ₛ₁⟨ 2 & 1 & ap-∘ (E.comp (F₁ f)) G.F₁ (F.pres-comp g h) ⟩
        ap G.F₁ (ap F.F₁ (C.assoc f g h)) ◃∙
        pres-comp f (C.comp g h) ◃∙
        ap (E.comp (F₁ f)) (ap G.F₁ (F.pres-comp g h)) ◃∙
        ap (E.comp (F₁ f)) (G.pres-comp (F.F₁ g) (F.F₁ h)) ◃∎
          =ₛ⟨ 2 & 2 & ∙-ap-seq (E.comp (F₁ f)) (pres-comp-seq g h) ⟩
        ap G.F₁ (ap F.F₁ (C.assoc f g h)) ◃∙
        pres-comp f (C.comp g h) ◃∙
        ap (E.comp (F₁ f)) (pres-comp g h) ◃∎
          =ₛ₁⟨ 0 & 1 & ∘-ap G.F₁ F.F₁ (C.assoc f g h) ⟩
        ap F₁ (C.assoc f g h) ◃∙
        pres-comp f (C.comp g h) ◃∙
        ap (E.comp (F₁ f)) (pres-comp g h) ◃∎ ∎ₛ

  composition : TwoSemiFunctor C E
  composition =
    record
    { F₀ = F₀
    ; F₁ = F₁
    ; pres-comp = pres-comp
    ; pres-comp-coh = pres-comp-coh
    }

open FunctorComposition
  renaming ( composition to comp-functors
           ; pres-comp-seq to comp-functors-pres-comp-seq
           ; pres-comp to comp-functors-pres-comp
           ; pres-comp-β to comp-functors-pres-comp-β
           ) public

infixr 80 _–F→_
_–F→_ = comp-functors
