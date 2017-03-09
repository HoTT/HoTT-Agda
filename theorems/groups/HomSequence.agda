{-# OPTIONS --without-K --rewriting #-}

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

{- maps between two hom sequences -}

infix 15 _↓|ᴳ
infixr 10 _↓⟨_⟩ᴳ_

data HomSeqMap {i₀ i₁} : {G₀ H₀ : Group i₀} {G₁ H₁ : Group i₁}
  → HomSequence G₀ H₀ → HomSequence G₁ H₁
  → (G₀ →ᴳ G₁) → (H₀ →ᴳ H₁) → Type (lsucc (lmax i₀ i₁)) where
  _↓|ᴳ : {G₀ : Group i₀} {G₁ : Group i₁} (ξ : G₀ →ᴳ G₁) → HomSeqMap (G₀ ⊣|ᴳ) (G₁ ⊣|ᴳ) ξ ξ
  _↓⟨_⟩ᴳ_ : {G₀ H₀ K₀ : Group i₀} {G₁ H₁ K₁ : Group i₁}
    → {φ : G₀ →ᴳ H₀} {seq₀ : HomSequence H₀ K₀}
    → {ψ : G₁ →ᴳ H₁} {seq₁ : HomSequence H₁ K₁}
    → (ξG : G₀ →ᴳ G₁) {ξH : H₀ →ᴳ H₁} {ξK : K₀ →ᴳ K₁}
    → CommSquareᴳ φ ψ ξG ξH
    → HomSeqMap seq₀ seq₁ ξH ξK
    → HomSeqMap (G₀ →⟨ φ ⟩ᴳ seq₀) (G₁ →⟨ ψ ⟩ᴳ seq₁) ξG ξK

HomSeqMap-snoc : ∀ {i₀ i₁} {G₀ H₀ K₀ : Group i₀} {G₁ H₁ K₁ : Group i₁}
  {seq₀ : HomSequence G₀ H₀} {seq₁ : HomSequence G₁ H₁}
  {φ₀ : H₀ →ᴳ K₀} {φ₁ : H₁ →ᴳ K₁}
  {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁} {ξK : K₀ →ᴳ K₁}
  → HomSeqMap seq₀ seq₁ ξG ξH
  → CommSquareᴳ φ₀ φ₁ ξH ξK
  → HomSeqMap (HomSeq-snoc seq₀ φ₀) (HomSeq-snoc seq₁ φ₁) ξG ξK
HomSeqMap-snoc (ξG ↓|ᴳ) □ = ξG ↓⟨ □ ⟩ᴳ _ ↓|ᴳ
HomSeqMap-snoc (ξG ↓⟨ □₁ ⟩ᴳ seq) □₂ = ξG ↓⟨ □₁ ⟩ᴳ HomSeqMap-snoc seq □₂

{- equivalences between two hom sequences -}

is-seqᴳ-equiv : ∀ {i₀ i₁} {G₀ H₀ : Group i₀} {G₁ H₁ : Group i₁}
  {seq₀ : HomSequence G₀ H₀} {seq₁ : HomSequence G₁ H₁}
  {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁}
  → HomSeqMap seq₀ seq₁ ξG ξH
  → Type (lmax i₀ i₁)
is-seqᴳ-equiv (ξ ↓|ᴳ) = is-equiv (GroupHom.f ξ)
is-seqᴳ-equiv (ξ ↓⟨ _ ⟩ᴳ seq) = is-equiv (GroupHom.f ξ) × is-seqᴳ-equiv seq

is-seqᴳ-equiv-snoc : ∀ {i₀ i₁} {G₀ H₀ K₀ : Group i₀} {G₁ H₁ K₁ : Group i₁}
  {seq₀ : HomSequence G₀ H₀} {seq₁ : HomSequence G₁ H₁}
  {φ₀ : H₀ →ᴳ K₀} {φ₁ : H₁ →ᴳ K₁}
  {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁} {ξK : K₀ →ᴳ K₁}
  {seq-map : HomSeqMap seq₀ seq₁ ξG ξH}
  {cs : CommSquareᴳ φ₀ φ₁ ξH ξK}
  → is-seqᴳ-equiv seq-map → is-equiv (GroupHom.f ξK)
  → is-seqᴳ-equiv (HomSeqMap-snoc seq-map cs)
is-seqᴳ-equiv-snoc {seq-map = ξG ↓|ᴳ} ξG-is-equiv ξH-is-equiv = ξG-is-equiv , ξH-is-equiv
is-seqᴳ-equiv-snoc {seq-map = ξG ↓⟨ _ ⟩ᴳ seq} (ξG-is-equiv , seq-is-equiv) ξH-is-equiv =
  ξG-is-equiv , is-seqᴳ-equiv-snoc seq-is-equiv ξH-is-equiv

private
  is-seqᴳ-equiv-head : ∀ {i₀ i₁} {G₀ H₀ : Group i₀} {G₁ H₁ : Group i₁}
    {seq₀ : HomSequence G₀ H₀} {seq₁ : HomSequence G₁ H₁}
    {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁}
    {seq-map : HomSeqMap seq₀ seq₁ ξG ξH}
    → is-seqᴳ-equiv seq-map → is-equiv (GroupHom.f ξG)
  is-seqᴳ-equiv-head {seq-map = ξ ↓|ᴳ} ise = ise
  is-seqᴳ-equiv-head {seq-map = ξ ↓⟨ _ ⟩ᴳ _} ise = fst ise

  is-seqᴳ-equiv-last : ∀ {i₀ i₁} {G₀ H₀ : Group i₀} {G₁ H₁ : Group i₁}
    {seq₀ : HomSequence G₀ H₀} {seq₁ : HomSequence G₁ H₁}
    {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁}
    {seq-map : HomSeqMap seq₀ seq₁ ξG ξH}
    → is-seqᴳ-equiv seq-map → is-equiv (GroupHom.f ξH)
  is-seqᴳ-equiv-last {seq-map = ξ ↓|ᴳ} ise = ise
  is-seqᴳ-equiv-last {seq-map = _ ↓⟨ _ ⟩ᴳ rest} (_ , rest-ise) = is-seqᴳ-equiv-last rest-ise

module is-seqᴳ-equiv {i₀ i₁} {G₀ H₀ : Group i₀} {G₁ H₁ : Group i₁}
  {seq₀ : HomSequence G₀ H₀} {seq₁ : HomSequence G₁ H₁}
  {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁}
  {seq-map : HomSeqMap seq₀ seq₁ ξG ξH}
  (seq-map-is-equiv : is-seqᴳ-equiv seq-map) where

  head = is-seqᴳ-equiv-head seq-map-is-equiv
  last = is-seqᴳ-equiv-last seq-map-is-equiv

HomSeqEquiv : ∀ {i₀ i₁} {G₀ H₀ : Group i₀} {G₁ H₁ : Group i₁}
  (seq₀ : HomSequence G₀ H₀) (seq₁ : HomSequence G₁ H₁)
  (ξG : G₀ →ᴳ G₁) (ξH : H₀ →ᴳ H₁) → Type (lsucc (lmax i₀ i₁))
HomSeqEquiv seq₀ seq₁ ξG ξH = Σ (HomSeqMap seq₀ seq₁ ξG ξH) is-seqᴳ-equiv

HomSeqEquiv-inverse : ∀ {i₀ i₁} {G₀ H₀ : Group i₀} {G₁ H₁ : Group i₁}
  {seq₀ : HomSequence G₀ H₀} {seq₁ : HomSequence G₁ H₁}
  {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁}
  (equiv : HomSeqEquiv seq₀ seq₁ ξG ξH)
  → HomSeqEquiv seq₁ seq₀
      (GroupIso.g-hom (ξG , is-seqᴳ-equiv-head (snd equiv)))
      (GroupIso.g-hom (ξH , is-seqᴳ-equiv-last (snd equiv)))
HomSeqEquiv-inverse ((ξ ↓|ᴳ) , ξ-ise) =
  (GroupIso.g-hom (ξ , ξ-ise) ↓|ᴳ) , is-equiv-inverse ξ-ise
HomSeqEquiv-inverse ((ξ ↓⟨ □ ⟩ᴳ rest) , (ξ-ise , rest-ise)) =
  (GroupIso.g-hom (ξ , ξ-ise)
    ↓⟨ CommSquareᴳ-inverse-v □ ξ-ise (is-seqᴳ-equiv-head rest-ise) ⟩ᴳ
  fst rest-inverse-equiv) ,
  is-equiv-inverse ξ-ise , snd rest-inverse-equiv
  where
    rest-inverse-equiv = HomSeqEquiv-inverse (rest , rest-ise)

{- Doesn't seem useful.

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

private
  hom-seq-map-index-type : ∀ {i₀ i₁} {G₀ H₀ : Group i₀} {G₁ H₁ : Group i₁}
    {seq₀ : HomSequence G₀ H₀} {seq₁ : HomSequence G₁ H₁}
    {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁}
    → ℕ → HomSeqMap seq₀ seq₁ ξG ξH → Type (lmax i₀ i₁)
  hom-seq-map-index-type _     (_ ↓|ᴳ) = Lift ⊤
  hom-seq-map-index-type O     (_↓⟨_⟩ᴳ_ {φ = φ} {ψ = ψ} ξG {ξH} _ _)
    = CommSquareᴳ φ ψ ξG ξH
  hom-seq-map-index-type (S n) (_ ↓⟨ _ ⟩ᴳ seq-map)
    = hom-seq-map-index-type n seq-map

abstract
  hom-seq-map-index : ∀ {i₀ i₁} {G₀ H₀ : Group i₀} {G₁ H₁ : Group i₁}
    {seq₀ : HomSequence G₀ H₀} {seq₁ : HomSequence G₁ H₁}
    {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁}
    (n : ℕ) (seq-map : HomSeqMap seq₀ seq₁ ξG ξH)
    → hom-seq-map-index-type n seq-map
  hom-seq-map-index _     (_ ↓|ᴳ) = lift tt
  hom-seq-map-index O     (_ ↓⟨ □ ⟩ᴳ _) = □
  hom-seq-map-index (S n) (_ ↓⟨ _ ⟩ᴳ seq-map)
    = hom-seq-map-index n seq-map

private
  hom-seq-equiv-index-type : ∀ {i₀ i₁} {G₀ H₀ : Group i₀} {G₁ H₁ : Group i₁}
    {seq₀ : HomSequence G₀ H₀} {seq₁ : HomSequence G₁ H₁}
    {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁}
    → ℕ → HomSeqMap seq₀ seq₁ ξG ξH → Type (lmax i₀ i₁)
  hom-seq-equiv-index-type {ξG = ξG} O _ = is-equiv (GroupHom.f ξG)
  hom-seq-equiv-index-type (S _) (_ ↓|ᴳ) = Lift ⊤
  hom-seq-equiv-index-type (S n) (_ ↓⟨ _ ⟩ᴳ seq-map)
    = hom-seq-equiv-index-type n seq-map

abstract
  hom-seq-equiv-index : ∀ {i₀ i₁} {G₀ H₀ : Group i₀} {G₁ H₁ : Group i₁}
    {seq₀ : HomSequence G₀ H₀} {seq₁ : HomSequence G₁ H₁}
    {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁}
    (n : ℕ) (seq-equiv : HomSeqEquiv seq₀ seq₁ ξG ξH)
    → hom-seq-equiv-index-type n (fst seq-equiv)
  hom-seq-equiv-index O     (seq-map , ise) = is-seqᴳ-equiv-head ise
  hom-seq-equiv-index (S _) ((_ ↓|ᴳ) , _) = lift tt
  hom-seq-equiv-index (S n) ((_ ↓⟨ _ ⟩ᴳ seq-map) , ise)
    = hom-seq-equiv-index n (seq-map , snd ise)
