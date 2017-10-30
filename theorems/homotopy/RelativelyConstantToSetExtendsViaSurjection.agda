{-# OPTIONS --without-K --rewriting #-}

open import HoTT
import homotopy.ConstantToSetExtendsToProp as ConstExt

module homotopy.RelativelyConstantToSetExtendsViaSurjection
  {i j k} {A : Type i} {B : Type j} {C : B → Type k}
  {{_ : ∀ {b} → is-set (C b)}}
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
        (lemma b) (lemma-const b)

  ext : Π B C
  ext b = CE.ext b (f-is-surj b)

  β : (a : A) → ext (f a) == g a
  β a = ap (CE.ext (f a))
    (prop-has-all-paths (f-is-surj (f a)) [ a , idp ])
