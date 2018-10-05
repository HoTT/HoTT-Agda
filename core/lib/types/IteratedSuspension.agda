{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NConnected
open import lib.types.Bool
open import lib.types.Nat
open import lib.types.Paths
open import lib.types.TLevel
open import lib.types.Suspension
open import lib.types.Truncation

module lib.types.IteratedSuspension where

Susp^ : ∀ {i} (n : ℕ) → Type i → Type i
Susp^ O X = X
Susp^ (S n) X = Susp (Susp^ n X)

Susp^-pt : ∀ {i} (n : ℕ) (A : Ptd i) → Susp^ n (de⊙ A)
Susp^-pt O A = pt A
Susp^-pt (S n) A = north

⊙Susp^ : ∀ {i} (n : ℕ) → Ptd i → Ptd i
⊙Susp^ n X = ptd (Susp^ n (de⊙ X)) (Susp^-pt n X)

abstract
  Susp^-conn : ∀ {i} (n : ℕ) {A : Type i} {m : ℕ₋₂}
    {{_ : is-connected m A}} → is-connected (⟨ n ⟩₋₂ +2+ m) (Susp^ n A)
  Susp^-conn O = ⟨⟩
  Susp^-conn (S n) = Susp-conn (Susp^-conn n)

  ⊙Susp^-conn' : ∀ {i} (n : ℕ) {A : Type i}
    {{_ : is-connected 0 A}} → is-connected ⟨ n ⟩ (Susp^ n A)
  ⊙Susp^-conn' O = ⟨⟩
  ⊙Susp^-conn' (S n) = Susp-conn (⊙Susp^-conn' n)

Susp^-+ : ∀ {i} (m n : ℕ) {A : Type i}
  → Susp^ m (Susp^ n A) == Susp^ (m + n) A
Susp^-+ O n = idp
Susp^-+ (S m) n = ap Susp (Susp^-+ m n)

Susp^-+-pt : ∀ {i} (m n : ℕ) {X : Ptd i}
  → Susp^-pt m (⊙Susp^ n X) == Susp^-pt (m + n) X [ idf _ ↓ Susp^-+ m n ]
Susp^-+-pt O n = idp
Susp^-+-pt (S m) n =
  ↓-ap-in (idf _) Susp (apd (λ A → north {A = A}) (Susp^-+ m n))

⊙Susp^-+ : ∀ {i} (m n : ℕ) {X : Ptd i}
  → ⊙Susp^ m (⊙Susp^ n X) == ⊙Susp^ (m + n) X
⊙Susp^-+ m n {X} = ptd= (Susp^-+ m n {de⊙ X}) (Susp^-+-pt m n)

Susp^-Trunc-swap : ∀ {i} (A : Type i) (n : ℕ) (m : ℕ₋₂)
  → Susp^ n (Trunc m A)
  → Trunc (⟨ n ⟩₋₂ +2+ m) (Susp^ n A)
Susp^-Trunc-swap A O m = idf _
Susp^-Trunc-swap A (S n) m =
  Susp-Trunc-swap (Susp^ n A) (⟨ n ⟩₋₂ +2+ m) ∘
  Susp-fmap (Susp^-Trunc-swap A n m)

Susp^-fmap : ∀ {i j} (n : ℕ) {A : Type i} {B : Type j}
  → (A → B) → Susp^ n A → Susp^ n B
Susp^-fmap O f = f
Susp^-fmap (S n) f = Susp-fmap (Susp^-fmap n f)

⊙Susp^-fmap : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → X ⊙→ Y → ⊙Susp^ n X ⊙→ ⊙Susp^ n Y
⊙Susp^-fmap O f = f
⊙Susp^-fmap (S n) f = ⊙Susp-fmap (Susp^-fmap n (fst f))

Susp^-fmap-idf : ∀ {i} (n : ℕ) (A : Type i)
  → Susp^-fmap n (idf A) == idf (Susp^ n A)
Susp^-fmap-idf O A = idp
Susp^-fmap-idf (S n) A = ↯ $
  Susp-fmap (Susp^-fmap n (idf A))
    =⟪ ap Susp-fmap (Susp^-fmap-idf n A) ⟫
  Susp-fmap (idf _)
    =⟪ λ= (Susp-fmap-idf _) ⟫
  idf (Susp^ (S n) A) ∎∎

⊙Susp^-fmap-idf : ∀ {i} (n : ℕ) (X : Ptd i)
  → ⊙Susp^-fmap n (⊙idf X) == ⊙idf (⊙Susp^ n X)
⊙Susp^-fmap-idf O X = idp
⊙Susp^-fmap-idf (S n) X =
  ap ⊙Susp-fmap (Susp^-fmap-idf n (de⊙ X)) ∙ ⊙Susp-fmap-idf (Susp^ n (de⊙ X))

Susp^-fmap-cst : ∀ {i j} (n : ℕ) {A : Type i} {Y : Ptd j}
  → Susp^-fmap n {A = A} (λ _ → pt Y) == (λ _ → pt (⊙Susp^ n Y))
Susp^-fmap-cst O = idp
Susp^-fmap-cst (S n) {A} {Y} = ↯ $
  Susp-fmap (Susp^-fmap n {A = A} (λ _ → pt Y))
    =⟪ ap Susp-fmap (Susp^-fmap-cst n) ⟫
  Susp-fmap (λ _ → pt (⊙Susp^ n Y))
    =⟪ λ= (Susp-fmap-cst (pt (⊙Susp^ n Y))) ⟫
  (λ _ → north) ∎∎

⊙Susp^-fmap-cst : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → ⊙Susp^-fmap n (⊙cst {X = X} {Y = Y}) == ⊙cst
⊙Susp^-fmap-cst O = idp
⊙Susp^-fmap-cst (S n) = ap ⊙Susp-fmap (Susp^-fmap-cst n) ∙ ⊙Susp-fmap-cst

Susp^-fmap-∘ : ∀ {i j k} (n : ℕ) {A : Type i} {B : Type j} {C : Type k}
  (g : B → C) (f : A → B)
  → Susp^-fmap n (g ∘ f) == Susp^-fmap n g ∘ Susp^-fmap n f
Susp^-fmap-∘ O g f = idp
Susp^-fmap-∘ (S n) g f =
  Susp-fmap (Susp^-fmap n (g ∘ f))
    =⟨ ap Susp-fmap (Susp^-fmap-∘ n g f) ⟩
  Susp-fmap (Susp^-fmap n g ∘ Susp^-fmap n f)
    =⟨ λ= (Susp-fmap-∘ (Susp^-fmap n g) (Susp^-fmap n f)) ⟩
  Susp^-fmap (S n) g ∘ Susp^-fmap (S n) f =∎

⊙Susp^-fmap-∘ : ∀ {i j k} (n : ℕ) {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
  (g : Y ⊙→ Z) (f : X ⊙→ Y)
  → ⊙Susp^-fmap n (g ⊙∘ f) == ⊙Susp^-fmap n g ⊙∘ ⊙Susp^-fmap n f
⊙Susp^-fmap-∘ O g f = idp
⊙Susp^-fmap-∘ (S n) g f =
  ap ⊙Susp-fmap (Susp^-fmap-∘ n (fst g) (fst f))
  ∙ ⊙Susp-fmap-∘ (Susp^-fmap n (fst g)) (Susp^-fmap n (fst f))

Susp^-Susp-split-iso : ∀ {i} (n : ℕ) (A : Type i)
  → Susp (Susp^ n A) ≃ Susp^ n (Susp A)
Susp^-Susp-split-iso O A = ide _
Susp^-Susp-split-iso (S n) A = Susp-emap (Susp^-Susp-split-iso n A)

⊙Susp^-Susp-split-iso : ∀ {i} (n : ℕ) (A : Type i)
  → ⊙Susp (Susp^ n A) ⊙≃ ⊙Susp^ n (⊙Susp A)
⊙Susp^-Susp-split-iso O A = ⊙ide _
⊙Susp^-Susp-split-iso (S n) A = ⊙Susp-emap (Susp^-Susp-split-iso n A)

⊙Sphere : (n : ℕ) → Ptd₀
⊙Sphere n = ⊙Susp^ n ⊙Bool

Sphere : (n : ℕ) → Type₀
Sphere n = de⊙ (⊙Sphere n)

abstract
  instance
    Sphere-conn : ∀ (n : ℕ) → is-connected ⟨ n ⟩₋₁ (Sphere n)
    Sphere-conn 0 = inhab-conn true
    Sphere-conn (S n) = Susp-conn (Sphere-conn n)

-- favonia: [S¹] has its own elim rules in Circle.agda.
⊙S⁰ = ⊙Sphere 0
⊙S¹ = ⊙Sphere 1
⊙S² = ⊙Sphere 2
⊙S³ = ⊙Sphere 3
S⁰ = Sphere 0
S¹ = Sphere 1
S² = Sphere 2
S³ = Sphere 3
