{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pi
open import lib.types.TwoSemiCategory
open import lib.two-semi-categories.FunCategory
open import lib.two-semi-categories.Functor
open import lib.two-semi-categories.FunctorInverse

module lib.two-semi-categories.DualCategory where

dual-cat : ∀ {i j} → TwoSemiCategory i j → TwoSemiCategory i j
dual-cat C =
  record
  { El = C.El
  ; Arr = λ x y → C.Arr y x
  ; Arr-level = λ x y → C.Arr-level y x
  ; two-semi-cat-struct =
    record
    { comp = λ f g → C.comp g f
    ; assoc = λ f g h → ! (C.assoc h g f)
    ; pentagon-identity = pentagon
    }
  }
  where
    module C = TwoSemiCategory C
    abstract
      pentagon : {z y x w v : C.El}
        (f : C.Arr y z) (g : C.Arr x y) (h : C.Arr w x) (i : C.Arr v w)
        → ! (C.assoc i h (C.comp g f)) ◃∙
          ! (C.assoc (C.comp i h) g f) ◃∎
          =ₛ
          ap (C.comp i) (! (C.assoc h g f)) ◃∙
          ! (C.assoc i (C.comp h g) f) ◃∙
          ap (λ s → C.comp s f) (! (C.assoc i h g)) ◃∎
      pentagon = λ f g h i →
        ! (C.assoc i h (C.comp g f)) ◃∙
        ! (C.assoc (C.comp i h) g f) ◃∎
          =ₛ⟨ ∙-!-seq (C.assoc (C.comp i h) g f ◃∙ C.assoc i h (C.comp g f) ◃∎) ⟩
        ! (C.assoc (C.comp i h) g f ∙ C.assoc i h (C.comp g f)) ◃∎
          =ₛ₁⟨ ap ! (=ₛ-out (C.pentagon-identity i h g f)) ⟩
        ! (ap (λ s → C.comp s f) (C.assoc i h g) ∙
           C.assoc i (C.comp h g) f ∙
           ap (C.comp i) (C.assoc h g f)) ◃∎
          =ₛ⟨ !-∙-seq $
              ap (λ s → C.comp s f) (C.assoc i h g) ◃∙
              C.assoc i (C.comp h g) f ◃∙
              ap (C.comp i) (C.assoc h g f) ◃∎ ⟩
        ! (ap (C.comp i) (C.assoc h g f)) ◃∙
        ! (C.assoc i (C.comp h g) f) ◃∙
        ! (ap (λ s → C.comp s f) (C.assoc i h g)) ◃∎
          =ₛ₁⟨ 0 & 1 & !-ap (C.comp i) (C.assoc h g f) ⟩
        ap (C.comp i) (! (C.assoc h g f)) ◃∙
        ! (C.assoc i (C.comp h g) f) ◃∙
        ! (ap (λ s → C.comp s f) (C.assoc i h g)) ◃∎
          =ₛ₁⟨ 2 & 1 & !-ap (λ s → C.comp s f) (C.assoc i h g) ⟩
        ap (C.comp i) (! (C.assoc h g f)) ◃∙
        ! (C.assoc i (C.comp h g) f) ◃∙
        ap (λ s → C.comp s f) (! (C.assoc i h g)) ◃∎ ∎ₛ

dual-functor-map : ∀ {i₁ j₁ i₂ j₂} {C : TwoSemiCategory i₁ j₁} {D : TwoSemiCategory i₂ j₂}
  → TwoSemiFunctor C D → TwoSemiFunctor (dual-cat C) (dual-cat D)
dual-functor-map {C = C} {D = D} F =
  record
  { F₀ = F.F₀
  ; F₁ = λ f → F.F₁ f
  ; pres-comp = λ f g → F.pres-comp g f
  ; pres-comp-coh = pres-comp-coh
  }
  where
    module F = TwoSemiFunctor F
    module C = TwoSemiCategory C
    module D = TwoSemiCategory D
    abstract
      pres-comp-coh : {w x y z : C.El} → (f : C.Arr y z) (g : C.Arr x y) (h : C.Arr w x)
        → F.pres-comp h (C.comp g f) ◃∙
          ap (D.comp (F.F₁ h)) (F.pres-comp g f) ◃∙
          ! (D.assoc (F.F₁ h) (F.F₁ g) (F.F₁ f)) ◃∎
          =ₛ
          ap (λ f' → F.F₁ f') (! (C.assoc h g f)) ◃∙
          F.pres-comp (C.comp h g) f ◃∙
          ap (λ s → D.comp s (F.F₁ f)) (F.pres-comp h g) ◃∎
      pres-comp-coh f g h =
        e₅₋₆ ◃∙ e₆₋₄ ◃∙ ! e₃₋₄ ◃∎
          =ₛ⟨ post-rotate'-seq-in {p = ! e₁₋₅ ◃∙ e₁₋₂ ◃∙ e₂₋₃ ◃∎} $
              pre-rotate-in $
              !ₛ $ F.pres-comp-coh h g f ⟩
        ! e₁₋₅ ◃∙ e₁₋₂ ◃∙ e₂₋₃ ◃∎
          =ₛ⟨ =ₛ-in $
              ap (λ s → s ∙ e₁₋₂ ∙ e₂₋₃) (!-ap (λ f' → F.F₁ f') (C.assoc h g f)) ⟩
        ap (λ f' → F.F₁ f') (! (C.assoc h g f)) ◃∙ e₁₋₂ ◃∙ e₂₋₃ ◃∎ ∎ₛ
        where
        e₁₋₂ = F.pres-comp (C.comp h g) f
        e₂₋₃ = ap (λ s → D.comp s (F.F₁ f)) (F.pres-comp h g)
        e₃₋₄ = D.assoc (F.F₁ h) (F.F₁ g) (F.F₁ f)
        e₁₋₅ = ap F.F₁ (C.assoc h g f)
        e₅₋₆ = F.pres-comp h (C.comp g f)
        e₆₋₄ = ap (D.comp (F.F₁ h)) (F.pres-comp g f)

from-double-dual : ∀ {i j} → (C : TwoSemiCategory i j)
  → TwoSemiFunctor (dual-cat (dual-cat C)) C
from-double-dual C =
  record
  { F₀ = λ x → x
  ; F₁ = λ f → f
  ; pres-comp = λ f g → idp
  ; pres-comp-coh = pres-comp-coh
  }
  where
    module C = TwoSemiCategory C
    abstract
      pres-comp-coh : ∀ {w x y z : C.El} (f : C.Arr w x) (g : C.Arr x y) (h : C.Arr y z)
        → idp ◃∙ idp ◃∙ C.assoc f g h ◃∎
          =ₛ
          ap (λ f → f) (! (! (C.assoc f g h))) ◃∙ idp ◃∙ idp ◃∎
      pres-comp-coh f g h = =ₛ-in $
        C.assoc f g h
          =⟨ ! (!-! (C.assoc f g h)) ⟩
        ! (! (C.assoc f g h))
          =⟨ ! (ap-idf _) ⟩
        ap (λ f → f) (! (! (C.assoc f g h)))
          =⟨ ! (∙-unit-r _) ⟩
        ap (λ f → f) (! (! (C.assoc f g h))) ∙ idp =∎

module _ {i j k} (A : Type i) (C : TwoSemiCategory j k) where

  private
    module C = TwoSemiCategory C

  swap-dual-fun-functor : TwoSemiFunctor (dual-cat (fun-cat A C)) (fun-cat A (dual-cat C))
  swap-dual-fun-functor =
    record
    { F₀ = λ x → x
    ; F₁ = λ f → f
    ; pres-comp = λ f g → idp
    ; pres-comp-coh = pres-comp-coh
    }
    where
      abstract
        pres-comp-coh : ∀ {w x y z : A → C.El}
          (f : ∀ a → C.Arr (x a) (w a))
          (g : ∀ a → C.Arr (y a) (x a))
          (h : ∀ a → C.Arr (z a) (y a))
          → idp ◃∙ idp ◃∙ λ= (λ a → ! (C.assoc (h a) (g a) (f a))) ◃∎
            =ₛ
            ap (λ x → x) (! (λ= (λ a → C.assoc (h a) (g a) (f a)))) ◃∙ idp ◃∙ idp ◃∎
        pres-comp-coh f g h =
          idp ◃∙ idp ◃∙ λ= (λ a → ! (C.assoc (h a) (g a) (f a))) ◃∎
            =ₛ⟨ 0 & 2 & =ₛ-in {t = []} idp ⟩
          λ= (λ a → ! (C.assoc (h a) (g a) (f a))) ◃∎
            =ₛ₁⟨ !-λ= (λ a → C.assoc (h a) (g a) (f a)) ⟩
          ! (λ= (λ a → C.assoc (h a) (g a) (f a))) ◃∎
            =ₛ₁⟨ ! (ap-idf _) ⟩
          ap (λ x → x) (! (λ= (λ a → C.assoc (h a) (g a) (f a)))) ◃∎
            =ₛ⟨ 1 & 0 & =ₛ-in {t = idp ◃∙ idp ◃∎} idp ⟩
          ap (λ x → x) (! (λ= (λ a → C.assoc (h a) (g a) (f a)))) ◃∙ idp ◃∙ idp ◃∎ ∎ₛ

  swap-fun-dual-functor : TwoSemiFunctor (fun-cat A (dual-cat C)) (dual-cat (fun-cat A C))
  swap-fun-dual-functor =
    record
    { F₀ = λ x → x
    ; F₁ = λ f → f
    ; pres-comp = λ f g → idp
    ; pres-comp-coh = pres-comp-coh
    }
    where
      abstract
        pres-comp-coh : ∀ {w x y z : A → C.El}
          (f : ∀ a → C.Arr (x a) (w a))
          (g : ∀ a → C.Arr (y a) (x a))
          (h : ∀ a → C.Arr (z a) (y a))
          → idp ◃∙ idp ◃∙ ! (λ= (λ a → C.assoc (h a) (g a) (f a))) ◃∎
            =ₛ
            ap (λ x → x) (λ= (λ a → ! (C.assoc (h a) (g a) (f a)))) ◃∙ idp ◃∙ idp ◃∎
        pres-comp-coh f g h =
          idp ◃∙ idp ◃∙ ! (λ= (λ a → C.assoc (h a) (g a) (f a))) ◃∎
            =ₛ⟨ 0 & 2 & =ₛ-in {t = []} idp ⟩
          ! (λ= (λ a → C.assoc (h a) (g a) (f a))) ◃∎
            =ₛ₁⟨ λ=-! (λ a → C.assoc (h a) (g a) (f a)) ⟩
          λ= (λ a → ! (C.assoc (h a) (g a) (f a))) ◃∎
            =ₛ₁⟨ ! (ap-idf _) ⟩
          ap (λ x → x) (λ= (λ a → ! (C.assoc (h a) (g a) (f a)))) ◃∎
            =ₛ⟨ 1 & 0 & =ₛ-in {t = idp ◃∙ idp ◃∎} idp ⟩
          ap (λ x → x) (λ= (λ a → ! (C.assoc (h a) (g a) (f a)))) ◃∙ idp ◃∙ idp ◃∎ ∎ₛ

  {-
  -- alternative definition for swap-fun-dual-functor:
  functor-inverse swap-dual-fun-functor
                  (idf-is-equiv (A → C.El))
                  (λ α β → idf-is-equiv (∀ a → C.Arr (β a) (α a)))
  -}
