{-# OPTIONS --without-K #-}

open import HoTT

{-
  Note: this module is for cohomology theories,
        so the commuting squares below do not
        care about the proof of pointedness,
        because any cohomology theory is independent
        of the possibly different proofs of pointedness.
-}

module homotopy.PtdMapSequence where

infix 15 _⊙⊣|
infixr 10 _⊙→⟨_⟩_

data PtdMapSequence {i} : (X : Ptd i) (Y : Ptd i) → Type (lsucc i) where
  _⊙⊣| : (X : Ptd i) → PtdMapSequence X X
  _⊙→⟨_⟩_ : (X : Ptd i) {Y Z : Ptd i}
    → (X ⊙→ Y) → PtdMapSequence Y Z
    → PtdMapSequence X Z

{- maps between two pointed map sequences -}

infix 15 _⊙↓|
infixr 10 _⊙↓⟨_⟩_

data PtdMapSeqMap {i₀ i₁} : {X₀ Y₀ : Ptd i₀} {X₁ Y₁ : Ptd i₁}
  (⊙seq₀ : PtdMapSequence X₀ Y₀) (⊙seq₁ : PtdMapSequence X₁ Y₁)
  (⊙hX : X₀ ⊙→ X₁) (⊙fY : Y₀ ⊙→ Y₁) → Type (lsucc (lmax i₀ i₁)) where
  _⊙↓| : {X₀ : Ptd i₀} {X₁ : Ptd i₁} (f : X₀ ⊙→ X₁) → PtdMapSeqMap (X₀ ⊙⊣|) (X₁ ⊙⊣|) f f
  _⊙↓⟨_⟩_ : ∀ {X₀ Y₀ Z₀ : Ptd i₀} {X₁ Y₁ Z₁ : Ptd i₁}
    → {⊙f₀ : X₀ ⊙→ Y₀} {⊙seq₀ : PtdMapSequence Y₀ Z₀}
    → {⊙f₁ : X₁ ⊙→ Y₁} {⊙seq₁ : PtdMapSequence Y₁ Z₁}
    → (⊙hX : X₀ ⊙→ X₁) {⊙hY : Y₀ ⊙→ Y₁} {⊙hZ : Z₀ ⊙→ Z₁}
    → CommSquare (fst ⊙f₀) (fst ⊙f₁) (fst ⊙hX) (fst ⊙hY)
    → PtdMapSeqMap ⊙seq₀ ⊙seq₁ ⊙hY ⊙hZ
    → PtdMapSeqMap (X₀ ⊙→⟨ ⊙f₀ ⟩ ⊙seq₀) (X₁ ⊙→⟨ ⊙f₁ ⟩ ⊙seq₁) ⊙hX ⊙hZ

{- equivalences between two pointed map sequences -}

is-⊙seq-equiv : ∀ {i₀ i₁} {X₀ Y₀ : Ptd i₀} {X₁ Y₁ : Ptd i₁}
  {⊙seq₀ : PtdMapSequence X₀ Y₀} {⊙seq₁ : PtdMapSequence X₁ Y₁}
  {⊙hX : X₀ ⊙→ X₁} {⊙hY : Y₀ ⊙→ Y₁}
  → PtdMapSeqMap ⊙seq₀ ⊙seq₁ ⊙hX ⊙hY
  → Type (lmax i₀ i₁)
is-⊙seq-equiv (⊙h ⊙↓|) = is-equiv (fst ⊙h)
is-⊙seq-equiv (⊙h ⊙↓⟨ _ ⟩ ⊙seq) = is-equiv (fst ⊙h) × is-⊙seq-equiv ⊙seq

PtdMapSeqEquiv : ∀ {i₀ i₁} {X₀ Y₀ : Ptd i₀} {X₁ Y₁ : Ptd i₁}
  (⊙seq₀ : PtdMapSequence X₀ Y₀) (⊙seq₁ : PtdMapSequence X₁ Y₁)
  (⊙hX : X₀ ⊙→ X₁) (⊙hY : Y₀ ⊙→ Y₁) → Type (lsucc (lmax i₀ i₁))
PtdMapSeqEquiv ⊙seq₀ ⊙seq₁ ⊙hX ⊙hY
  = Σ (PtdMapSeqMap ⊙seq₀ ⊙seq₁ ⊙hX ⊙hY) is-⊙seq-equiv

{- Doesn't seem useful.

infix 15 _⊙↕⊣|
infixr 10 _⊙↕⟨_⟩↕_

_⊙↕⊣| : ∀ {i} {X₀ X₁ : Ptd i} (⊙eq : X₀ ⊙≃ X₁)
  → PtdMapSequenceEquiv (X₀ ⊙⊣|) (X₁ ⊙⊣|) (⊙–> ⊙eq) (⊙–> ⊙eq)
⊙eq ⊙↕⊣| = (⊙–> ⊙eq ⊙↓⊣|) , snd ⊙eq

_⊙↕⟨_⟩↕_ : ∀ {i} {X₀ X₁ : Ptd i} → (⊙eqX : X₀ ⊙≃ X₁)
           → ∀ {Y₀ Y₁ : Ptd i} {⊙f : X₀ ⊙→ Y₀} {⊙g : X₁ ⊙→ Y₁} {⊙eqY : Y₀ ⊙≃ Y₁}
           → ⊙CommutingSquare ⊙f ⊙g (⊙–> ⊙eqX) (⊙–> ⊙eqY)
           → ∀ {Z₀ Z₁ : Ptd i} {⊙eqZ : Z₀ ⊙≃ Z₁} {⊙seq₀ : PtdMapSequence Y₀ Z₀} {⊙seq₁ : PtdMapSequence Y₁ Z₁}
           → PtdMapSequenceEquiv ⊙seq₀ ⊙seq₁ (⊙–> ⊙eqY) (⊙–> ⊙eqZ)
           → PtdMapSequenceEquiv (X₀ ⊙⟨ ⊙f ⟩→ ⊙seq₀) (X₁ ⊙⟨ ⊙g ⟩→ ⊙seq₁) (⊙–> ⊙eqX) (⊙–> ⊙eqZ)
(⊙hX , hX-is-equiv) ⊙↕⟨ sqr ⟩↕ (⊙seq-map , ⊙seq-map-is-equiv) =
  (⊙hX ⊙↓⟨ sqr ⟩↓ ⊙seq-map) , hX-is-equiv , ⊙seq-map-is-equiv
-}

{-
  commutes' : ⊙<– ⊙codomain-is-related ⊙∘ g
           == f ⊙∘ ⊙<– ⊙domain-is-related
  commutes' = ap (⊙<– ⊙codomain-is-related ⊙∘_)
                ( ! (⊙∘-unit-r g)
                ∙ ap (g ⊙∘_) (! $ ⊙<–-inv-r ⊙domain-is-related)
                ∙ ! (⊙∘-assoc g (⊙–> ⊙domain-is-related) (⊙<– ⊙domain-is-related))
                ∙ ap (_⊙∘ ⊙<– ⊙domain-is-related) (! commutes)
                ∙ ⊙∘-assoc (⊙–> ⊙codomain-is-related) f (⊙<– ⊙domain-is-related))
            ∙ ! (⊙∘-assoc (⊙<– ⊙codomain-is-related) (⊙–> ⊙codomain-is-related) (f ⊙∘ ⊙<– ⊙domain-is-related))
            ∙ ap (_⊙∘ (f ⊙∘ ⊙<– ⊙domain-is-related)) (⊙<–-inv-l ⊙codomain-is-related)
            ∙ ⊙∘-unit-l (f ⊙∘ ⊙<– ⊙domain-is-related)
-}
