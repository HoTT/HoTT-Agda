{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NConnected
open import lib.types.Bool
open import lib.types.FunctionSeq
open import lib.types.Pointed
open import lib.types.Suspension.Core
open import lib.types.TLevel

module lib.types.Suspension.Iterated where

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

Susp^-fmap : ∀ {i j} (n : ℕ) {A : Type i} {B : Type j}
  → (A → B) → Susp^ n A → Susp^ n B
Susp^-fmap O f = f
Susp^-fmap (S n) f = Susp-fmap (Susp^-fmap n f)

⊙Susp^-fmap-pt : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  (f : X ⊙→ Y)
  → Susp^-fmap n (fst f) (pt (⊙Susp^ n X)) == pt (⊙Susp^ n Y)
⊙Susp^-fmap-pt O f = snd f
⊙Susp^-fmap-pt (S n) f = idp

⊙Susp^-fmap : ∀ {i j} (n : ℕ) {X : Ptd i} {Y : Ptd j}
  → X ⊙→ Y → ⊙Susp^ n X ⊙→ ⊙Susp^ n Y
⊙Susp^-fmap n f = Susp^-fmap n (fst f) , ⊙Susp^-fmap-pt n f

Susp^-fmap-idf : ∀ {i} (n : ℕ) (A : Type i)
  → Susp^-fmap n (idf A) == idf (Susp^ n A)
Susp^-fmap-idf O A = idp
Susp^-fmap-idf (S n) A = ↯ $
  Susp-fmap (Susp^-fmap n (idf A))
    =⟪ ap Susp-fmap (Susp^-fmap-idf n A) ⟫
  Susp-fmap (idf _)
    =⟪ λ= (Susp-fmap-idf _) ⟫
  idf (Susp^ (S n) A) ∎∎

transport-Susp^ : ∀ {i} {A B : Type i} (n : ℕ) (p : A == B)
  → transport (Susp^ n) p == Susp^-fmap n (coe p)
transport-Susp^ n idp = ! (Susp^-fmap-idf n _)

⊙Susp^-fmap-idf : ∀ {i} (n : ℕ) (X : Ptd i)
  → ⊙Susp^-fmap n (⊙idf X) ◃⊙idf =⊙∘ ⊙idf-seq
⊙Susp^-fmap-idf O X = =⊙∘-in idp
⊙Susp^-fmap-idf (S n) X =
  ⊙Susp^-fmap (S n) (⊙idf X) ◃⊙idf
    =⊙∘₁⟨ ap ⊙Susp-fmap (Susp^-fmap-idf n (de⊙ X)) ⟩
  ⊙Susp-fmap (idf _) ◃⊙idf
    =⊙∘⟨ ⊙Susp-fmap-idf (Susp^ n (de⊙ X)) ⟩
  ⊙idf-seq ∎⊙∘

⊙transport-⊙Susp^ : ∀ {i} {X Y : Ptd i} (n : ℕ) (p : X == Y)
  → ⊙transport (⊙Susp^ n) p == ⊙Susp^-fmap n (⊙coe p)
⊙transport-⊙Susp^ n p@idp = ! (=⊙∘-out (⊙Susp^-fmap-idf n _))

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

⊙Susp^-fmap-seq : ∀ {i} (n : ℕ) {X : Ptd i} {Y : Ptd i}
  → X ⊙–→ Y
  → ⊙Susp^ n X ⊙–→ ⊙Susp^ n Y
⊙Susp^-fmap-seq n ⊙idf-seq = ⊙idf-seq
⊙Susp^-fmap-seq n (f ◃⊙∘ fs) = ⊙Susp^-fmap n f ◃⊙∘ ⊙Susp^-fmap-seq n fs

⊙Susp^-fmap-seq-∘ : ∀ {i} (n : ℕ) {X : Ptd i} {Y : Ptd i} (fs : X ⊙–→ Y)
  → ⊙Susp^-fmap n (⊙compose fs) ◃⊙idf =⊙∘ ⊙Susp^-fmap-seq n fs
⊙Susp^-fmap-seq-∘ n ⊙idf-seq = ⊙Susp^-fmap-idf n _
⊙Susp^-fmap-seq-∘ n (f ◃⊙∘ fs) = =⊙∘-in $
  ⊙Susp^-fmap n (f ⊙∘ ⊙compose fs)
    =⟨ ⊙Susp^-fmap-∘ n f (⊙compose fs) ⟩
  ⊙Susp^-fmap n f ⊙∘ ⊙Susp^-fmap n (⊙compose fs)
    =⟨ ap (⊙Susp^-fmap n f ⊙∘_) (=⊙∘-out (⊙Susp^-fmap-seq-∘ n fs)) ⟩
  ⊙Susp^-fmap n f ⊙∘ ⊙compose (⊙Susp^-fmap-seq n fs) =∎

⊙Susp^-fmap-seq-=⊙∘ : ∀ {i} (n : ℕ) {X : Ptd i} {Y : Ptd i} {fs gs : X ⊙–→ Y}
  → fs =⊙∘ gs
  → ⊙Susp^-fmap-seq n fs =⊙∘ ⊙Susp^-fmap-seq n gs
⊙Susp^-fmap-seq-=⊙∘ n {fs = fs} {gs = gs} p =
  ⊙Susp^-fmap-seq n fs
    =⊙∘⟨ !⊙∘ $ ⊙Susp^-fmap-seq-∘ n fs ⟩
  ⊙Susp^-fmap n (⊙compose fs) ◃⊙idf
    =⊙∘₁⟨ ap (⊙Susp^-fmap n) (=⊙∘-out p) ⟩
  ⊙Susp^-fmap n (⊙compose gs) ◃⊙idf
    =⊙∘⟨ ⊙Susp^-fmap-seq-∘ n gs ⟩
  ⊙Susp^-fmap-seq n gs ∎⊙∘

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
