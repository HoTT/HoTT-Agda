open import HoTT
open import cohomology.FunctionOver

module cohomology.Exactness where

module _ {i j k} {G : Group i} {H : Group j} {K : Group k}
  (φ : G →ᴳ H) (ψ : H →ᴳ K) where

  private
    module G = Group G
    module H = Group H
    module K = Group K
    module φ = GroupHom φ
    module ψ = GroupHom ψ

  {- in image of φ ⇒ in kernel of ψ -}
  is-exact-itok : Type (lmax k (lmax j i))
  is-exact-itok = (h : H.El)
    → Trunc ⟨-1⟩ (Σ G.El (λ g → φ.f g == h)) → ψ.f h == K.ident

  {- in kernel of ψ ⇒ in image of φ -}
  is-exact-ktoi : Type (lmax k (lmax j i))
  is-exact-ktoi = (h : H.El)
    → ψ.f h == K.ident → Trunc ⟨-1⟩ (Σ G.El (λ g → φ.f g == h))

  record is-exact : Type (lmax k (lmax j i)) where
    field
      itok : is-exact-itok
      ktoi : is-exact-ktoi

  open is-exact public

  {- an equivalent version of is-exact-ktoi  -}
  itok-alt-in : ((g : G.El) → ψ.f (φ.f g) == K.ident) → is-exact-itok
  itok-alt-in r h = Trunc-rec (K.El-level _ _) (λ {(g , p) → ap ψ.f (! p) ∙ r g})

  itok-alt-out : is-exact-itok → ((g : G.El) → ψ.f (φ.f g) == K.ident)
  itok-alt-out s g = s (φ.f g) [ g , idp ]

{- Convenient notation for sequences of homomorphisms -}

infix 15 _⊣|
infixr 10 _⟨_⟩→_

data HomSequence {i} : Group i → Group i → Type (lsucc i) where
  _⊣| : (G : Group i) → HomSequence G G
  _⟨_⟩→_ : (G : Group i) {H K : Group i} (φ : G →ᴳ H)
             → HomSequence H K → HomSequence G K

data SequencePath {i} : {G₁ H₁ G₂ H₂ : Group i}
  (S₁ : HomSequence G₁ H₁) (S₂ : HomSequence G₂ H₂)
  → G₁ == G₂ → H₁ == H₂ → Type (lsucc i) where
  seq-path-z : ∀ {G₁ G₂} (p : G₁ == G₂) → SequencePath (G₁ ⊣|) (G₂ ⊣|) p p
  seq-path-s : ∀ {G₁ G₂} (pG : G₁ == G₂)
    {H₁ K₁ H₂ K₂ : Group i} {φ₁ : G₁ →ᴳ H₁} {φ₂ : G₂ →ᴳ H₂}
    {S₁ : HomSequence H₁ K₁} {S₂ : HomSequence H₂ K₂}
    {pH : H₁ == H₂} {pK : K₁ == K₂}
    (over : φ₁ == φ₂ [ uncurry _→ᴳ_ ↓ pair×= pG pH ])
    → SequencePath S₁ S₂ pH pK
    → SequencePath (G₁ ⟨ φ₁ ⟩→ S₁) (G₂ ⟨ φ₂ ⟩→ S₂) pG pK

infix 15 _↓⊣|
infixr 10 _↓⟨_⟩↓_

data SequenceIso {i j} : {G₁ H₁ : Group i} {G₂ H₂ : Group j}
  (S₁ : HomSequence G₁ H₁) (S₂ : HomSequence G₂ H₂)
  → G₁ ≃ᴳ G₂ → H₁ ≃ᴳ H₂ → Type (lsucc (lmax i j)) where
  _↓⊣| : ∀ {G₁ G₂} (iso : G₁ ≃ᴳ G₂) → SequenceIso (G₁ ⊣|) (G₂ ⊣|) iso iso
  _↓⟨_⟩↓_ : ∀ {G₁ G₂} (isoG : G₁ ≃ᴳ G₂)
    {H₁ K₁ : Group i} {H₂ K₂ : Group j} {φ₁ : G₁ →ᴳ H₁} {φ₂ : G₂ →ᴳ H₂}
    {S₁ : HomSequence H₁ K₁} {S₂ : HomSequence H₂ K₂}
    {isoH : H₁ ≃ᴳ H₂} {isoK : K₁ ≃ᴳ K₂}
    (over : fst isoH ∘ᴳ φ₁ == φ₂ ∘ᴳ fst isoG)
    → SequenceIso S₁ S₂ isoH isoK
    → SequenceIso (G₁ ⟨ φ₁ ⟩→ S₁) (G₂ ⟨ φ₂ ⟩→ S₂) isoG isoK

seq-iso-to-path : ∀ {i} {G₁ H₁ G₂ H₂ : Group i}
  {S₁ : HomSequence G₁ H₁} {S₂ : HomSequence G₂ H₂}
  {isoG : G₁ ≃ᴳ G₂} {isoH : H₁ ≃ᴳ H₂}
  → SequenceIso S₁ S₂ isoG isoH
  → SequencePath S₁ S₂ (group-ua isoG) (group-ua isoH)
seq-iso-to-path (iso ↓⊣|) = seq-path-z (group-ua iso)
seq-iso-to-path (iso ↓⟨ over ⟩↓ si') =
  seq-path-s (group-ua iso)
    (hom-over-isos $ function-over-equivs _ _ $ ap GroupHom.f over)
    (seq-iso-to-path si')

sequence-path-ua : ∀ {i} {G₁ H₁ G₂ H₂ : Group i}
  {S₁ : HomSequence G₁ H₁} {S₂ : HomSequence G₂ H₂}
  (pG : G₁ == G₂) (pH : H₁ == H₂) → SequencePath S₁ S₂ pG pH
  → S₁ == S₂ [ uncurry HomSequence ↓ pair×= pG pH ]
sequence-path-ua idp .idp (seq-path-z .idp) = idp
sequence-path-ua {G₁ = G₁} idp idp
  (seq-path-s .idp {φ₁ = φ₁} {pH = idp} idp sp') =
    ap (λ S' → G₁ ⟨ φ₁ ⟩→ S') (sequence-path-ua idp idp sp')

sequence-iso-ua : ∀ {i} {G₁ H₁ G₂ H₂ : Group i}
  {S₁ : HomSequence G₁ H₁} {S₂ : HomSequence G₂ H₂}
  (isoG : G₁ ≃ᴳ G₂) (isoH : H₁ ≃ᴳ H₂) → SequenceIso S₁ S₂ isoG isoH
  → S₁ == S₂ [ uncurry HomSequence ↓ pair×= (group-ua isoG) (group-ua isoH) ]
sequence-iso-ua isoG isoH si = sequence-path-ua _ _ (seq-iso-to-path si)

data is-exact-seq {i} : {G H : Group i} → HomSequence G H → Type (lsucc i) where
  exact-seq-zero : {G : Group i} → is-exact-seq (G ⊣|)
  exact-seq-one : {G H : Group i} {φ : G →ᴳ H} → is-exact-seq (G ⟨ φ ⟩→ H ⊣|)
  exact-seq-two : {G H K J : Group i} {φ : G →ᴳ H} {ψ : H →ᴳ K}
    {diag : HomSequence K J} → is-exact φ ψ
    → is-exact-seq (H ⟨ ψ ⟩→ diag) → is-exact-seq (G ⟨ φ ⟩→ H ⟨ ψ ⟩→ diag)

private
  exact-get-type : ∀ {i} {G H : Group i} → HomSequence G H → ℕ → Type i
  exact-get-type (G ⊣|) _ = Lift Unit
  exact-get-type (G ⟨ φ ⟩→ H ⊣|) _ = Lift Unit
  exact-get-type (G ⟨ φ ⟩→ (H ⟨ ψ ⟩→ s)) O = is-exact φ ψ
  exact-get-type (_ ⟨ _ ⟩→ s) (S n) = exact-get-type s n

exact-get : ∀ {i} {G H : Group i} {diag : HomSequence G H}
  → is-exact-seq diag → (n : ℕ) → exact-get-type diag n
exact-get exact-seq-zero _ = lift unit
exact-get exact-seq-one _ = lift unit
exact-get (exact-seq-two ex s) O = ex
exact-get (exact-seq-two ex s) (S n) = exact-get s n

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
    exact-seq-two ie (exact-build-helper (H ⟨ ψ ⟩→ s) ies)

exact-build : ∀ {i} {G H : Group i} (seq : HomSequence G H)
  → hlist-curry-type (exact-build-arg-type seq) (λ _ → is-exact-seq seq)
exact-build seq = hlist-curry (exact-build-helper seq)

private
  hom-seq-snoc : ∀ {i} {G H K : Group i}
    → HomSequence G H → (H →ᴳ K) → HomSequence G K
  hom-seq-snoc (G ⊣|) ψ = G ⟨ ψ ⟩→ _ ⊣|
  hom-seq-snoc (G ⟨ φ ⟩→ s) ψ = G ⟨ φ ⟩→ hom-seq-snoc s ψ

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
  exact-concat {seq₁ = G ⟨ ψ ⟩→ H ⊣|} (exact-seq-two ex _) es₂ =
    exact-seq-two ex es₂
  exact-concat {seq₁ = G ⟨ ψ ⟩→ H ⟨ χ ⟩→ s} (exact-seq-two ex es₁) es₂ =
    exact-seq-two ex (exact-concat {seq₁ = H ⟨ χ ⟩→ s} es₁ es₂)
