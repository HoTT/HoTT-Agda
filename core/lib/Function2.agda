{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Truncation

module lib.Function2 where

is-surj : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) → Type (lmax i j)
is-surj {A = A} f = ∀ b → Trunc -1 (hfiber f b)

module _ {i j k} {A : Type i} {B : Type j} {C : Type k}
  {f : A → B} {g : B → C} where
  abstract
    ∘-is-surj : is-surj g → is-surj f → is-surj (g ∘ f)
    ∘-is-surj g-is-surj f-is-surj c =
      Trunc-rec
        (λ{(b , gb=c) →
          Trunc-rec
          (λ{(a , fa=b) → [ a , ap g fa=b ∙ gb=c ]})
          (f-is-surj b)})
        (g-is-surj c)

module _ {i j} {A : Type i} {B : Type j} {f : A → B} where
  abstract
    equiv-is-surj : is-equiv f → is-surj f
    equiv-is-surj f-is-equiv b = [ g b , f-g b ]
      where open is-equiv f-is-equiv

is-cs-equiv : ∀ {i₀ i₁ j₀ j₁}
  {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
  {f₀ : A₀ → B₀} {f₁ : A₁ → B₁} {hA : A₀ → A₁} {hB : B₀ → B₁}
  → CommSquare f₀ f₁ hA hB → Type (lmax (lmax i₀ i₁) (lmax j₀ j₁))
is-cs-equiv {hA = hA} {hB} _ = Σ (is-equiv hA) (λ _ → is-equiv hB)

CommSquareEquiv : ∀ {i₀ i₁ j₀ j₁}
  {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
  (f₀ : A₀ → B₀) (f₁ : A₁ → B₁) (hA : A₀ → A₁) (hB : B₀ → B₁)
  → Type (lmax (lmax i₀ i₁) (lmax j₀ j₁))
CommSquareEquiv f₀ f₁ hA hB = Σ (CommSquare f₀ f₁ hA hB) is-cs-equiv

is-⊙cs-equiv : ∀ {i₀ i₁ j₀ j₁}
  {X₀ : Ptd i₀} {X₁ : Ptd i₁} {Y₀ : Ptd j₀} {Y₁ : Ptd j₁}
  {f₀ : X₀ ⊙→ Y₀} {f₁ : X₁ ⊙→ Y₁} {hX : X₀ ⊙→ X₁} {hY : Y₀ ⊙→ Y₁}
  → ⊙CommSquare f₀ f₁ hX hY → Type (lmax (lmax i₀ i₁) (lmax j₀ j₁))
is-⊙cs-equiv {hX = hX} {hY} _ = Σ (is-equiv (fst hX)) (λ _ → is-equiv (fst hY))

⊙CommSquareEquiv : ∀ {i₀ i₁ j₀ j₁}
  {X₀ : Ptd i₀} {X₁ : Ptd i₁} {Y₀ : Ptd j₀} {Y₁ : Ptd j₁}
  (f₀ : X₀ ⊙→ Y₀) (f₁ : X₁ ⊙→ Y₁) (hX : X₀ ⊙→ X₁) (hY : Y₀ ⊙→ Y₁)
  → Type (lmax (lmax i₀ i₁) (lmax j₀ j₁))
⊙CommSquareEquiv f₀ f₁ hX hY = Σ (⊙CommSquare f₀ f₁ hX hY) is-⊙cs-equiv
