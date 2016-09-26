{-# OPTIONS --without-K #-}

open import HoTT

module groups.HomSequence where

infix 15 _⊣|ᴳ
infixr 10 _→⟨_⟩ᴳ_

data HomSequence {i} : (G : Group i) (H : Group i) → Type (lsucc i) where
  _⊣|ᴳ : (G : Group i) → HomSequence G G
  _→⟨_⟩ᴳ_ : (G : Group i) {H K : Group i}
    → (G →ᴳ H) → HomSequence H K
    → HomSequence G K

HomSeq-++ : ∀ {i} {G H K : Group i}
  → HomSequence G H → HomSequence H K → HomSequence G K
HomSeq-++ (_ ⊣|ᴳ) seq = seq
HomSeq-++ (_ →⟨ φ ⟩ᴳ seq₁) seq₂ = _ →⟨ φ ⟩ᴳ HomSeq-++ seq₁ seq₂

HomSeq-snoc : ∀ {i} {G H K : Group i}
  → HomSequence G H → (H →ᴳ K) → HomSequence G K
HomSeq-snoc seq φ = HomSeq-++ seq (_ →⟨ φ ⟩ᴳ _ ⊣|ᴳ)

{- maps between two homs -}

record HomCommSquare {i₀ i₁ j₀ j₁}
  {G₀ : Group i₀} {G₁ : Group i₁} {H₀ : Group j₀} {H₁ : Group j₁}
  (φ₀ : G₀ →ᴳ H₀) (φ₁ : G₁ →ᴳ H₁) (ξG : G₀ →ᴳ G₁) (ξH : H₀ →ᴳ H₁)
  : Type (lmax (lmax i₀ i₁) (lmax j₀ j₁)) where

  field
    commutes : ∀ g₀ → GroupHom.f (ξH ∘ᴳ φ₀) g₀ == GroupHom.f (φ₁ ∘ᴳ ξG) g₀

commutesᴳ = HomCommSquare.commutes

abstract
  HomComm-∘h : ∀ {i₀ i₁ i₂ j₀ j₁ j₂}
    {G₀ : Group i₀} {G₁ : Group i₁} {G₂ : Group i₂}
    {H₀ : Group j₀} {H₁ : Group j₁} {H₂ : Group j₂}
    {φ₀ : G₀ →ᴳ H₀} {φ₁ : G₁ →ᴳ H₁} {φ₂ : G₂ →ᴳ H₂}
    {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁}
    {ζG : G₁ →ᴳ G₂} {ζH : H₁ →ᴳ H₂}
    → HomCommSquare φ₀ φ₁ ξG ξH
    → HomCommSquare φ₁ φ₂ ζG ζH
    → HomCommSquare φ₀ φ₂ (ζG ∘ᴳ ξG) (ζH ∘ᴳ ξH)
  HomComm-∘h {ξG = ξG} {ζH = ζH} s₀₁ s₁₂ = record {
    commutes = λ g₀ → ap (GroupHom.f ζH) (commutesᴳ s₀₁ g₀)
                    ∙ commutesᴳ s₁₂ (GroupHom.f ξG g₀)}

{- maps between two hom sequences -}

infix 15 _↓|ᴳ
infixr 10 _↓⟨_⟩ᴳ_

data HomSeqMap {i} : {G₀ G₁ H₀ H₁ : Group i}
  → HomSequence G₀ H₀ → HomSequence G₁ H₁
  → (G₀ →ᴳ G₁) → (H₀ →ᴳ H₁) → Type (lsucc i) where
  _↓|ᴳ : {G₀ G₁ : Group i} (ξ : G₀ →ᴳ G₁) → HomSeqMap (G₀ ⊣|ᴳ) (G₁ ⊣|ᴳ) ξ ξ
  _↓⟨_⟩ᴳ_ : {G₀ G₁ H₀ H₁ K₀ K₁ : Group i}
    → {φ : G₀ →ᴳ H₀} {seq₀ : HomSequence H₀ K₀}
    → {ψ : G₁ →ᴳ H₁} {seq₁ : HomSequence H₁ K₁}
    → (ξG : G₀ →ᴳ G₁) {ξH : H₀ →ᴳ H₁} {ξK : K₀ →ᴳ K₁}
    → HomCommSquare φ ψ ξG ξH
    → HomSeqMap seq₀ seq₁ ξH ξK
    → HomSeqMap (G₀ →⟨ φ ⟩ᴳ seq₀) (G₁ →⟨ ψ ⟩ᴳ seq₁) ξG ξK

{- equivalences between two hom sequences -}

is-equiv-seqᴳ : ∀ {i} {G₀ G₁ H₀ H₁ : Group i}
  {seq₀ : HomSequence G₀ H₀} {seq₁ : HomSequence G₁ H₁}
  {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁}
  → HomSeqMap seq₀ seq₁ ξG ξH
  → Type i
is-equiv-seqᴳ (ξ ↓|ᴳ) = is-equiv (GroupHom.f ξ)
is-equiv-seqᴳ (ξ ↓⟨ _ ⟩ᴳ seq) = is-equiv (GroupHom.f ξ) × is-equiv-seqᴳ seq

is-equiv-seqᴳ-head : ∀ {i} {G₀ G₁ H₀ H₁ : Group i}
  {seq₀ : HomSequence G₀ H₀} {seq₁ : HomSequence G₁ H₁}
  {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁}
  {seq : HomSeqMap seq₀ seq₁ ξG ξH}
  → is-equiv-seqᴳ seq → is-equiv (GroupHom.f ξG)
is-equiv-seqᴳ-head {seq = ξ ↓|ᴳ} ise = ise
is-equiv-seqᴳ-head {seq = ξ ↓⟨ _ ⟩ᴳ seq} ise = fst ise

{- Doesn't seem useful.

HomSeqEquiv : ∀ {i} {G₀ G₁ H₀ H₁ : Group i}
  (seq₀ : HomSequence G₀ H₀) (seq₁ : HomSequence G₁ H₁)
  (ξG : G₀ →ᴳ G₁) (ξH : H₀ →ᴳ H₁) → Type (lsucc i)
HomSeqEquiv seq₀ seq₁ ξG ξH
  = Σ (HomSeqMap seq₀ seq₁ ξG ξH) is-equiv-seqᴳ

infix 15 _↕|ᴳ
infixr 10 _↕⟨_⟩ᴳ_

_↕|ᴳ : ∀ {i} {G₀ G₁ : Group i} (iso : G₀ ≃ᴳ G₁)
  → HomSeqEquiv (G₀ ⊣|ᴳ) (G₁ ⊣|ᴳ) (fst iso) (fst iso)
iso ↕|ᴳ = (fst iso ↓|ᴳ) , snd iso

_↕⟨_⟩ᴳ_ : ∀ {i} {G₀ G₁ H₀ H₁ K₀ K₁ : Group i}
  → {φ : G₀ →ᴳ H₀} {seq₀ : HomSequence H₀ K₀}
  → {ψ : G₁ →ᴳ H₁} {seq₁ : HomSequence H₁ K₁}
  → (isoG : G₀ ≃ᴳ G₁) {isoH : H₀ ≃ᴳ H₁} {isoK : K₀ ≃ᴳ K₁}
  → HomCommSquare φ ψ (fst isoG) (fst isoH)
  → HomSeqEquiv seq₀ seq₁ (fst isoH) (fst isoK)
  → HomSeqEquiv (G₀ →⟨ φ ⟩ᴳ seq₀) (G₁ →⟨ ψ ⟩ᴳ seq₁) (fst isoG) (fst isoK)
(ξG , hG-is-equiv) ↕⟨ sqr ⟩ᴳ (seq-map , seq-map-is-equiv) =
  (ξG ↓⟨ sqr ⟩ᴳ seq-map) , hG-is-equiv , seq-map-is-equiv
-}
