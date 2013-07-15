{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Nat
open import lib.types.TLevel
open import lib.types.Truncation

module homotopy.LoopSpace where

Ω^ : ∀ {i} (n : ℕ) (A : Type i) (a : A) → Type i
Ω^ O A a = A
Ω^ (S n) A a = Ω^ n (a == a) idp

idp^ : ∀ {i} (n : ℕ) (A : Type i) (a : A) → Ω^ n A a
idp^ O A a = a
idp^ (S n) A a = idp^ n (a == a) idp

ap^ : ∀ {i j} (n : ℕ) {A : Type i} {B : Type j} {a : A}
 (f : A → B) → Ω^ n A a → Ω^ n B (f a)
ap^ O {a = a} f x = f x
ap^ (S n) {a = a} f p = ap^ n (ap f) p

Ω^-outer : ∀ {i} (n : ℕ) (A : Type i) (a : A) 
  → Ω^ (S n) A a == Path (idp^ n A a) (idp^ n A a)
Ω^-outer O A a = idp
Ω^-outer (S n) A a = Ω^-outer n (a == a) idp

Ω^-level-in : ∀ {i} (m : ℕ₋₂) (n : ℕ) (A : Type i) (a : A)
  → (has-level ((n -2) +2+ m) A → has-level m (Ω^ n A a))
Ω^-level-in m O A a pA = pA
Ω^-level-in m (S n) A a pA = Ω^-level-in m n (a == a) idp (pA a a)

Ω^-–>-equiv : ∀ {i j} (n : ℕ) {A : Type i} {B : Type j} (e : A ≃ B) (a : A)
  → Ω^ n A a ≃ Ω^ n B (–> e a)
Ω^-–>-equiv O e a = e
Ω^-–>-equiv (S n) e a = Ω^-–>-equiv n (equiv-ap e a a) idp

Ω^-coe-path : ∀ {i} (n : ℕ) {A B : Type i} (p : A == B) (a : A)
  → Ω^ n A a == Ω^ n B (coe p a)
Ω^-coe-path _ idp _ = idp

Trunc-Ω^-equiv : ∀ {i} (m : ℕ₋₂) (n : ℕ) (A : Type i) (a : A)
  → Trunc m (Ω^ n A a) ≃ Ω^ n (Trunc ((n -2) +2+ m) A) [ a ]
Trunc-Ω^-equiv m O A a = ide _
Trunc-Ω^-equiv m (S n) A a = 
  Ω^-–>-equiv n ((Trunc=-equiv [ _ ] [ _ ])⁻¹) [ idp ] 
  ∘e (Trunc-Ω^-equiv m n (a == a) idp)

Trunc-Ω^-path : ∀ {i} (m : ℕ₋₂) (n : ℕ) (A : Type i) (a : A)
  → Trunc m (Ω^ n A a) == Ω^ n (Trunc ((n -2) +2+ m) A) [ a ]
Trunc-Ω^-path m n A a = ua $ (Trunc-Ω^-equiv m n A a)

π : ∀ {i} (n : ℕ) (A : Type i) (a : A) → Type i
π n A a = Trunc ⟨0⟩ (Ω^ n A a)

π-Trunc-≤T : ∀ {i} (n : ℕ) (m : ℕ₋₂) (A : Type i) (a : A) → (⟨ n ⟩ ≤T m) 
  → π n (Trunc m A) [ a ] == π n A a
π-Trunc-≤T n m A a lte = 
  π n (Trunc m A) [ a ]
    =⟨ ap (λ t → π n (Trunc t A) [ a ]) 
          (! (snd w) ∙ +2+-comm (fst w) ⟨ n ⟩ ∙ nlemma n (fst w)) ⟩
  π n (Trunc ((n -2) +2+ (S (S (fst w)))) A) [ a ]
    =⟨ ap (Trunc ⟨0⟩) (! (Trunc-Ω^-path (S (S (fst w))) n A a)) ⟩
  Trunc ⟨0⟩ (Trunc (S (S (fst w))) (Ω^ n A a))
    =⟨ ua $ fuse-Trunc _ ⟨0⟩ (S (S (fst w))) ⟩
  Trunc ⟨0⟩ (Ω^ n A a) ∎
  where
    w : Σ ℕ₋₂ (λ k → k +2+ ⟨ n ⟩ == m)
    w = ≤T-witness lte

    nlemma : (n : ℕ) (k : ℕ₋₂) → ⟨ n ⟩ +2+ k == (n -2) +2+ (S (S k))
    nlemma O k = idp
    nlemma (S n) k = ap S (nlemma n k)

