{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.RibbonCover
import homotopy.CoverClassification

module homotopy.CoverClassificationCat {i} (A∙ : Ptd i)
  (A-conn : is-connected 0 (fst A∙)) where

  open Cover
  open Gset
  open homotopy.CoverClassification A∙ A-conn

  private
    A : Type i
    A = fst A∙
    a₁ : A
    a₁ = snd A∙
    π1A = fundamental-group A∙

  -- A covering space constructed from a G-set.
  cover-hom-to-gset-hom : ∀ {j}
    → {cov₁ cov₂ : Cover A j}
    → CoverHom cov₁ cov₂
    → GsetHom (cover-to-gset cov₁) (cover-to-gset cov₂)
  cover-hom-to-gset-hom {cov₁ = cov₁}{cov₂} f = record
    { f = f a₁
    ; pres-act = λ l x → lemma₂ x l
    }
    where
      lemma₁ : ∀ x {a₂} (p : a₁ == a₂)
        → f a₂ (transport (Fiber cov₁) p x)
        == transport (Fiber cov₂) p (f a₁ x)
      lemma₁ _ idp = idp

      lemma₂ : ∀ x {a₂} (p : a₁ =₀ a₂)
        → f a₂ (transport₀ (Fiber cov₁) (Fiber-level cov₁ a₂) p x)
        == transport₀ (Fiber cov₂) (Fiber-level cov₂ a₂) p (f a₁ x)
      lemma₂ x {a₂} = Trunc-elim
        (λ p → =-preserves-level 0 (Fiber-level cov₂ a₂))
        (lemma₁ x {a₂})

  gset-hom-to-cover-hom : ∀ {j}
    → {gset₁ gset₂ : Gset π1A j}
    → GsetHom gset₁ gset₂
    → CoverHom (gset-to-cover gset₁) (gset-to-cover gset₂)
  gset-hom-to-cover-hom {gset₁ = gset₁}{gset₂} (gset-hom f pres-act) a₂ =
    Ribbon-rec
      {P = Ribbon A∙ gset₂ a₂}
      Ribbon-level
      (λ el p → trace (f el) p)
      (λ el loop p →
        trace (f (act gset₁ el loop)) p
          =⟨ pres-act loop el |in-ctx (λ x → trace x p) ⟩
        trace (act gset₂ (f el) loop) p
          =⟨ paste (f el) loop p ⟩
        trace (f el) (loop ∙₀ p)
          ∎)
