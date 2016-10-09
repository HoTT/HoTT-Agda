{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Pi
open import lib.types.Pointed
open import lib.types.Sigma

module lib.types.PointedSigma where

⊙Σ : ∀ {i j} (X : Ptd i) → (fst X → Ptd j) → Ptd (lmax i j)
⊙Σ (A , a₀) Y = ⊙[ Σ A (fst ∘ Y) , (a₀ , snd (Y a₀)) ]

infixr 80 _⊙×_
_⊙×_ : ∀ {i j} → Ptd i → Ptd j → Ptd (lmax i j)
X ⊙× Y = ⊙Σ X (λ _ → Y)

-- XXX Do we really need two versions of [⊙fst]?
⊙fstᵈ : ∀ {i j} {X : Ptd i} (Y : fst X → Ptd j) → ⊙Σ X Y ⊙→ X
⊙fstᵈ Y = (fst , idp)

⊙fst : ∀ {i j} {X : Ptd i} {Y : Ptd j} → X ⊙× Y ⊙→ X
⊙fst = ⊙fstᵈ _

⊙snd : ∀ {i j} {X : Ptd i} {Y : Ptd j} → X ⊙× Y ⊙→ Y
⊙snd = (snd , idp)

⊙diag : ∀ {i} {X : Ptd i} → X ⊙→ X ⊙× X
⊙diag = ((λ x → (x , x)) , idp)

⊙fanout-pt : ∀ {i j} {A : Type i} {B : Type j}
  {a₀ a₁ : A} (p : a₀ == a₁) {b₀ b₁ : B} (q : b₀ == b₁)
  → (a₀ , b₀) == (a₁ , b₁) :> A × B
⊙fanout-pt = pair×=

⊙fanout : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  → X ⊙→ Y → X ⊙→ Z → X ⊙→ Y ⊙× Z
⊙fanout (f , fpt) (g , gpt) = fanout f g , ⊙fanout-pt fpt gpt

⊙fst-fanout : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (f : X ⊙→ Y) (g : X ⊙→ Z)
  → ⊙fst ⊙∘ ⊙fanout f g == f
⊙fst-fanout (f , idp) (g , idp) = idp

⊙snd-fanout : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (f : X ⊙→ Y) (g : X ⊙→ Z)
  → ⊙snd ⊙∘ ⊙fanout f g == g
⊙snd-fanout (f , idp) (g , idp) = idp

⊙fanout-pre∘ : ∀ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (f : Y ⊙→ Z) (g : Y ⊙→ W) (h : X ⊙→ Y)
  → ⊙fanout f g ⊙∘ h == ⊙fanout (f ⊙∘ h) (g ⊙∘ h)
⊙fanout-pre∘ (f , idp) (g , idp) (h , idp) = idp

⊙×-fmap : ∀ {i i' j j'} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j} {Y' : Ptd j'}
  → X ⊙→ X' → Y ⊙→ Y' → X ⊙× Y ⊙→ X' ⊙× Y'
⊙×-fmap (f , fpt) (g , gpt) = ×-fmap f g , pair×= fpt gpt

⊙×-emap : ∀ {i i' j j'} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j} {Y' : Ptd j'}
  → X ⊙≃ X' → Y ⊙≃ Y' → X ⊙× Y ⊙≃ X' ⊙× Y'
⊙×-emap (F , F-ise) (G , G-ise) = ⊙×-fmap F G , ×-isemap F-ise G-ise
