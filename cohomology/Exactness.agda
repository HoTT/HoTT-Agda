open import HoTT

module cohomology.Exactness where

module _ {i j k} {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (F : fst (X ∙→ Y)) (G : fst (Y ∙→ Z)) where

  private
    f = fst F
    g = fst G

  {- in image of F ⇒ in kernel of G -}
  is-exact-itok : Type (lmax k (lmax j i))
  is-exact-itok = (y : fst Y) → Trunc ⟨-1⟩ (Σ (fst X) (λ x → f x == y))
    → g y == snd Z

  {- in kernel of G ⇒ in image of F -}
  is-exact-ktoi : Type (lmax k (lmax j i))
  is-exact-ktoi = (y : fst Y) → g y == snd Z
    → Trunc ⟨-1⟩ (Σ (fst X) (λ x → f x == y))

  record is-exact : Type (lmax k (lmax j i)) where
    field
      itok : is-exact-itok
      ktoi : is-exact-ktoi

  open is-exact public

  {- an equivalent version of is-exact-ktoi if Z is a set -}
  itok-alt-in : has-level ⟨0⟩ (fst Z)
    → ((x : fst X) → g (f x) == snd Z) → is-exact-itok
  itok-alt-in pZ h y = Trunc-rec (pZ _ _)
    (λ {(x , p) → ap g (! p) ∙ h x})

  itok-alt-out : is-exact-itok → ((x : fst X) → g (f x) == snd Z)
  itok-alt-out h x = h (f x) [ x , idp ]

{- Convenient notation for exact sequences. At the moment this is only set
   up for exact sequences of groups. Do we care about the general case?    -}

infix 2 _⊣|
infixr 2 _⟨_⟩→_

data ExactDiag {i} : Group i → Group i → Type (lsucc i) where
  _⊣| : (G : Group i) → ExactDiag G G
  _⟨_⟩→_ : (G : Group i) {H K : Group i} (φ : GroupHom G H)
             → ExactDiag H K → ExactDiag G K

data ExactSeq {i} : {G H : Group i} → ExactDiag G H → Type (lsucc i) where
  exact-seq-zero : {G : Group i} → ExactSeq (G ⊣|)
  exact-seq-one : {G H : Group i} {φ : GroupHom G H} → ExactSeq (G ⟨ φ ⟩→ H ⊣|)
  exact-seq-two : {G H K J : Group i} {φ : GroupHom G H} {ψ : GroupHom H K}
    {diag : ExactDiag K J} → is-exact (GroupHom.ptd-f φ) (GroupHom.ptd-f ψ)
    → ExactSeq (H ⟨ ψ ⟩→ diag) → ExactSeq (G ⟨ φ ⟩→ H ⟨ ψ ⟩→ diag)

private
  exact-get-type : ∀ {i} {G H : Group i} → ExactDiag G H → ℕ → Type i
  exact-get-type (G ⊣|) _ = Lift Unit
  exact-get-type (G ⟨ φ ⟩→ H ⊣|) _ = Lift Unit
  exact-get-type (G ⟨ φ ⟩→ (H ⟨ ψ ⟩→ s)) O =
    is-exact (GroupHom.ptd-f φ) (GroupHom.ptd-f ψ)
  exact-get-type (_ ⟨ _ ⟩→ s) (S n) = exact-get-type s n

exact-get : ∀ {i} {G H : Group i} {diag : ExactDiag G H}
  → ExactSeq diag → (n : ℕ) → exact-get-type diag n
exact-get exact-seq-zero _ = lift unit
exact-get exact-seq-one _ = lift unit
exact-get (exact-seq-two ex s) O = ex
exact-get (exact-seq-two ex s) (S n) = exact-get s n

private
  exact-build-arg-type : ∀ {i} {G H : Group i} → ExactDiag G H → List (Type i)
  exact-build-arg-type (G ⊣|) = nil
  exact-build-arg-type (G ⟨ φ ⟩→ H ⊣|) = nil
  exact-build-arg-type (G ⟨ φ ⟩→ H ⟨ ψ ⟩→ s) =
    is-exact (GroupHom.ptd-f φ) (GroupHom.ptd-f ψ)
    :: exact-build-arg-type (H ⟨ ψ ⟩→ s)

  exact-build-helper : ∀ {i} {G H : Group i} (diag : ExactDiag G H)
    → HList (exact-build-arg-type diag) → ExactSeq diag
  exact-build-helper (G ⊣|) nil = exact-seq-zero
  exact-build-helper (G ⟨ φ ⟩→ H ⊣|) nil = exact-seq-one
  exact-build-helper (G ⟨ φ ⟩→ H ⟨ ψ ⟩→ s) (ie :: ies) =
    exact-seq-two ie (exact-build-helper (H ⟨ ψ ⟩→ s) ies)

exact-build : ∀ {i} {G H : Group i} (diag : ExactDiag G H)
  → hlist-curry-type (exact-build-arg-type diag) (λ _ → ExactSeq diag)
exact-build diag = hlist-curry (exact-build-helper diag)

private
  exact-snoc-diag : ∀ {i} {G H K : Group i}
    → ExactDiag G H → GroupHom H K → ExactDiag G K
  exact-snoc-diag (G ⊣|) ψ = G ⟨ ψ ⟩→ _ ⊣|
  exact-snoc-diag (G ⟨ φ ⟩→ s) ψ = G ⟨ φ ⟩→ exact-snoc-diag s ψ

  exact-concat-diag : ∀ {i} {G H K : Group i}
    → ExactDiag G H → ExactDiag H K → ExactDiag G K
  exact-concat-diag (G ⊣|) s₂ = s₂
  exact-concat-diag (G ⟨ φ ⟩→ s₁) s₂ = G ⟨ φ ⟩→ (exact-concat-diag s₁ s₂)

abstract
  exact-concat : ∀ {i} {G H K L : Group i}
    {diag₁ : ExactDiag G H} {φ : GroupHom H K} {diag₂ : ExactDiag K L}
    → ExactSeq (exact-snoc-diag diag₁ φ) → ExactSeq (H ⟨ φ ⟩→ diag₂)
    → ExactSeq (exact-concat-diag diag₁ (H ⟨ φ ⟩→ diag₂))
  exact-concat {diag₁ = G ⊣|} exact-seq-one es₂ = es₂
  exact-concat {diag₁ = G ⟨ ψ ⟩→ H ⊣|} (exact-seq-two ex _) es₂ =
    exact-seq-two ex es₂
  exact-concat {diag₁ = G ⟨ ψ ⟩→ H ⟨ χ ⟩→ s} (exact-seq-two ex es₁) es₂ =
    exact-seq-two ex (exact-concat {diag₁ = H ⟨ χ ⟩→ s} es₁ es₂)
