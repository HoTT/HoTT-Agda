{-# OPTIONS --without-K --rewriting #-}

open import HoTT
import homotopy.ConstantToSetExtendsToProp as ConstExt

module homotopy.RelativelyConstantToSetExtendsViaSurjection
  {i j k} {A : Type i} {B : Type j} {C : B → Type k}
  (C-is-set : ∀ b → is-set (C b))
  (f : A → B) (f-is-surj : is-surj f)
  (g : (a : A) → C (f a))
  (g-is-const : ∀ a₁ a₂ → (p : f a₁ == f a₂) → g a₁ == g a₂ [ C ↓ p ])
  where

{-
  (b : A) ----> [ hfiber f b ] ----?----> C ?
                      ^
                      |
                  hfiber f b
-}

  private
    lemma : ∀ b → hfiber f b → C b
    lemma b (a , fa=b) = transport C fa=b (g a)

    lemma-const : ∀ b → (h₁ h₂ : hfiber f b) → lemma b h₁ == lemma b h₂
    lemma-const ._ (a₁ , fa₁=fa₂) (a₂ , idp) =
      to-transp (g-is-const a₁ a₂ fa₁=fa₂)

    module CE (b : B) =
      ConstExt {A = hfiber f b} {B = C b}
        (C-is-set b) (lemma b) (lemma-const b) 

  surj-ext : Π B C 
  surj-ext b = CE.cst-extend b (f-is-surj b)

  surj-ext-β : (a : A) → surj-ext (f a) == g a
  surj-ext-β a = ap (CE.cst-extend (f a))
    (prop-has-all-paths Trunc-level (f-is-surj (f a)) [ a , idp ])
