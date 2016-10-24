open import HoTT
-- open import homotopy.FunctionOver
open import groups.Exactness
open import groups.HomSequence

module groups.ExactSequence where

is-exact-seq : ∀ {i} {G H : Group i}
  → HomSequence G H → Type i
is-exact-seq (_ ⊣|ᴳ) = Lift ⊤
is-exact-seq (_ →⟨ φ ⟩ᴳ _ ⊣|ᴳ) = Lift ⊤
is-exact-seq (_ →⟨ φ ⟩ᴳ _ →⟨ ψ ⟩ᴳ seq) =
  is-exact φ ψ × is-exact-seq (_ →⟨ ψ ⟩ᴳ seq)

ExactSequence : ∀ {i} (G H : Group i) → Type (lsucc i)
ExactSequence G H = Σ (HomSequence G H) is-exact-seq

{- equivalences preserve exactness -}

abstract
  seq-equiv-preserves-exact : ∀ {i₀ i₁} {G₀ H₀ : Group i₀} {G₁ H₁ : Group i₁}
    {seq₀ : HomSequence G₀ H₀} {seq₁ : HomSequence G₁ H₁}
    {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁}
    → HomSeqEquiv seq₀ seq₁ ξG ξH
    → is-exact-seq seq₀ → is-exact-seq seq₁
  seq-equiv-preserves-exact ((_ ↓|ᴳ) , _) _ = lift tt
  seq-equiv-preserves-exact ((_ ↓⟨ _ ⟩ᴳ _ ↓|ᴳ) , _) _ = lift tt
  seq-equiv-preserves-exact
    ( (ξG ↓⟨ φ□ ⟩ᴳ _↓⟨_⟩ᴳ_ ξH {ξK} ψ□ seq-map)
    , (ξG-ise , ξH-ise , seq-map-ise))
    (φ₀-ψ₀-is-exact , ψ₀-seq₀-is-exact-seq) =
      equiv-preserves-exact
        φ□ ψ□ ξG-ise ξH-ise (is-seqᴳ-equiv.head seq-map-ise)
        φ₀-ψ₀-is-exact ,
      seq-equiv-preserves-exact
        ((ξH ↓⟨ ψ□ ⟩ᴳ seq-map) , (ξH-ise , seq-map-ise))
        ψ₀-seq₀-is-exact-seq

{-
  hom-seq-equiv-preserves'-exact : ∀ {i} {G₀ G₁ H₀ H₁ : Group i}
    {seq₀ : HomSequence G₀ H₀} {seq₁ : HomSequence G₁ H₁}
    {ξG : G₀ →ᴳ G₁} {ξH : H₀ →ᴳ H₁} (seq-map : HomSeqMap seq₀ seq₁ ξG ξH)
    → is-seqᴳ-equiv seq-map → is-exact-seq seq₁ → is-exact-seq seq₀
  hom-seq-equiv-preserves'-exact :
-}

private
  exact-seq-index-type : ∀ {i} {G H : Group i} → ℕ → HomSequence G H → Type i
  exact-seq-index-type _ (G ⊣|ᴳ) = Lift ⊤
  exact-seq-index-type _ (G →⟨ φ ⟩ᴳ H ⊣|ᴳ) = Lift ⊤
  exact-seq-index-type O (G →⟨ φ ⟩ᴳ H →⟨ ψ ⟩ᴳ s) = is-exact φ ψ
  exact-seq-index-type (S n) (_ →⟨ _ ⟩ᴳ s) = exact-seq-index-type n s

exact-seq-index : ∀ {i} {G H : Group i}
  → (n : ℕ) (seq : ExactSequence G H)
  → exact-seq-index-type n (fst seq)
exact-seq-index _     ((G ⊣|ᴳ) , _) = lift tt
exact-seq-index _     ((G →⟨ φ ⟩ᴳ H ⊣|ᴳ) , _) = lift tt
exact-seq-index O     ((G →⟨ φ ⟩ᴳ H →⟨ ψ ⟩ᴳ seq) , ise-seq) = fst ise-seq
exact-seq-index (S n) ((G →⟨ φ ⟩ᴳ H →⟨ ψ ⟩ᴳ seq) , ise-seq) =
  exact-seq-index n ((H →⟨ ψ ⟩ᴳ seq) , snd ise-seq)

{-
private
  exact-build-arg-type : ∀ {i} {G H : Group i} → HomSequence G H → List (Type i)
  exact-build-arg-type (G ⊣|) = nil
  exact-build-arg-type (G ⟨ φ ⟩→ H ⊣|) = nil
  exact-build-arg-type (G ⟨ φ ⟩→ H ⟨ ψ ⟩→ s) =
    is-exact φ ψ :: exact-build-arg-type (H ⟨ ψ ⟩→ s)

  exact-build-helper : ∀ {i} {G H : Group i} (seq : HomSequence G H)
    → HList (exact-build-arg-type seq) → is-exact-seq seq
  exact-build-helper (G ⊣|) nil = exact-seq-zero
  exact-build-helper (G ⟨ φ ⟩→ H ⊣|) nil = exact-seq-one
  exact-build-helper (G ⟨ φ ⟩→ H ⟨ ψ ⟩→ s) (ie :: ies) =
    exact-seq-more ie (exact-build-helper (H ⟨ ψ ⟩→ s) ies)

exact-build : ∀ {i} {G H : Group i} (seq : HomSequence G H)
  → hlist-curry-type (exact-build-arg-type seq) (λ _ → is-exact-seq seq)
exact-build seq = hlist-curry (exact-build-helper seq)

hom-seq-concat : ∀ {i} {G H K : Group i}
  → HomSequence G H → HomSequence H K → HomSequence G K
hom-seq-concat (G ⊣|) s₂ = s₂
hom-seq-concat (G ⟨ φ ⟩→ s₁) s₂ = G ⟨ φ ⟩→ (hom-seq-concat s₁ s₂)

abstract
  exact-concat : ∀ {i} {G H K L : Group i}
    {seq₁ : HomSequence G H} {φ : H →ᴳ K} {seq₂ : HomSequence K L}
    → is-exact-seq (hom-seq-snoc seq₁ φ) → is-exact-seq (H ⟨ φ ⟩→ seq₂)
    → is-exact-seq (hom-seq-concat seq₁ (H ⟨ φ ⟩→ seq₂))
  exact-concat {seq₁ = G ⊣|} exact-seq-one es₂ = es₂
  exact-concat {seq₁ = G ⟨ ψ ⟩→ H ⊣|} (exact-seq-more ex _) es₂ =
    exact-seq-more ex es₂
  exact-concat {seq₁ = G ⟨ ψ ⟩→ H ⟨ χ ⟩→ s} (exact-seq-more ex es₁) es₂ =
    exact-seq-more ex (exact-concat {seq₁ = H ⟨ χ ⟩→ s} es₁ es₂)
-}
