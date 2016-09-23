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
⊙fstᵈ : ∀ {i j} {X : Ptd i} (Y : fst X → Ptd j) → fst (⊙Σ X Y ⊙→ X)
⊙fstᵈ Y = (fst , idp)

⊙fst : ∀ {i j} {X : Ptd i} {Y : Ptd j} → fst (X ⊙× Y ⊙→ X)
⊙fst = ⊙fstᵈ _

⊙snd : ∀ {i j} {X : Ptd i} {Y : Ptd j} → fst (X ⊙× Y ⊙→ Y)
⊙snd = (snd , idp)

⊙diag : ∀ {i} {X : Ptd i} → fst (X ⊙→ X ⊙× X)
⊙diag = ((λ x → (x , x)) , idp)

⊙fanout : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  → fst (X ⊙→ Y) → fst (X ⊙→ Z) → fst (X ⊙→ Y ⊙× Z)
⊙fanout (f , fpt) (g , gpt) = fanout f g , pair×= fpt gpt

⊙fst-fanout : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (f : fst (X ⊙→ Y)) (g : fst (X ⊙→ Z))
  → ⊙fst ⊙∘ ⊙fanout f g == f
⊙fst-fanout (f , idp) (g , idp) = idp

⊙snd-fanout : ∀ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (f : fst (X ⊙→ Y)) (g : fst (X ⊙→ Z))
  → ⊙snd ⊙∘ ⊙fanout f g == g
⊙snd-fanout (f , idp) (g , idp) = idp

⊙fanout-pre∘ : ∀ {i j k l} {X : Ptd i} {Y : Ptd j} {Z : Ptd k} {W : Ptd l}
  (f : fst (Y ⊙→ Z)) (g : fst (Y ⊙→ W)) (h : fst (X ⊙→ Y))
  → ⊙fanout f g ⊙∘ h == ⊙fanout (f ⊙∘ h) (g ⊙∘ h)
⊙fanout-pre∘ (f , idp) (g , idp) (h , idp) = idp

⊙×-fmap : ∀ {i i' j j'} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j} {Y' : Ptd j'}
  → fst (X ⊙→ X') → fst (Y ⊙→ Y') → fst (X ⊙× Y ⊙→ X' ⊙× Y')
⊙×-fmap (f , fpt) (g , gpt) = ×-fmap f g , pair×= fpt gpt

⊙×-emap : ∀ {i i' j j'} {X : Ptd i} {X' : Ptd i'} {Y : Ptd j} {Y' : Ptd j'}
  → X ⊙≃ X' → Y ⊙≃ Y' → X ⊙× Y ⊙≃ X' ⊙× Y'
⊙×-emap (F , F-ise) (G , G-ise) = ⊙×-fmap F G , ×-isemap F-ise G-ise
