{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.Freudenthal

module homotopy.IteratedSuspension where

Ptd-Susp^ : ∀ {i} (n : ℕ) → Ptd i → Ptd i
Ptd-Susp^ O X = X
Ptd-Susp^ (S n) X = Ptd-Susp (Ptd-Susp^ n X)

-- Susp^ : ∀ {i} (n : ℕ) → Type i → Type i
-- Susp^ O A = A
-- Susp^ (S n) A = Suspension (Susp^ n A)

-- north^ : ∀ {i} (n : ℕ) {A : Type i} (a : A) → Susp^ n A
-- north^ O a = a
-- north^ (S n) {A = A} a = north (Susp^ n A)

-- Susp^-conn : ∀ {i} (n : ℕ) {A : Type i} {m : ℕ₋₂}
--   → is-connected m A → is-connected ((n -2) +2+ m) (Susp^ n A)
-- Susp^-conn O cA = cA
-- Susp^-conn (S n) cA = Susp-conn (Susp^-conn n cA)

Ptd-Susp^-conn : ∀ {i} (n : ℕ) {X : Ptd i} {m : ℕ₋₂}
  → is-connected m (fst X) → is-connected ((n -2) +2+ m) (fst (Ptd-Susp^ n X))
Ptd-Susp^-conn O cX = cX
Ptd-Susp^-conn (S n) cX = Susp-conn (Ptd-Susp^-conn n cX)

{- πΣ (S k) (Ptd-Susp^ (S n) X) == πΣ k (Ptd-Susp^ n X),
   where n = S n' and k = S k' -}
module Susp^Stable {i} (X : Ptd i) (cX : is-connected ⟨0⟩ (fst X))
  (n' : ℕ) (k' : ℕ) (kle : S k' ≤ (S n') *2) where
  
  {- need k,n ≥ 1 -}
  k : ℕ
  k = S k'

  n : ℕ
  n = S n'

  {- some numeric computations -}
  private
    kle' : ⟨ k ⟩ ≤T S ((n -2) +2+ S (n -2))
    kle' = ≤T-trans (⟨⟩-monotone-≤ kle) (inl (lemma n'))
      where lemma : (n' : ℕ) → ⟨ S n' *2 ⟩ == S ((S n' -2) +2+ S (S n' -2))
            lemma O = idp
            lemma (S n') = ap S (ap S (lemma n') 
                                 ∙ ! (+2+-βr (S (S n') -2) (S (S n') -2)))


    nlemma₁ : (n : ℕ) → (n -2) +2+ ⟨0⟩ == S (S (n -2))
    nlemma₁ n = +2+-comm (n -2) ⟨0⟩

    nlemma₂ : (k : ℕ) → (k -2) +2+ ⟨0⟩ == ⟨ k ⟩
    nlemma₂ O = idp
    nlemma₂ (S k) = ap S (nlemma₂ k)

  private
    module F = FreudenthalIso 
      (n -2) k kle' (Ptd-Susp^ n X)
      (transport (λ t → is-connected t (fst (Ptd-Susp^ n X)))
                 (nlemma₁ n) (Ptd-Susp^-conn n cX))

  stable : π (S k) (Ptd-Susp^ (S n) X) == π k (Ptd-Susp^ n X)
  stable = 
    π (S k) (Ptd-Susp^ (S n) X)
      =⟨ π-inner-iso k (Ptd-Susp^ (S n) X) ⟩
    π k (Ptd-Ω (Ptd-Susp^ (S n) X)) 
      =⟨ ! (π-Trunc-shift-iso k (Ptd-Ω (Ptd-Susp^ (S n) X))) ⟩
    Ω^-group k (Ptd-Trunc ⟨ k ⟩ (Ptd-Ω (Ptd-Susp^ (S n) X))) Trunc-level
      =⟨ ! F.iso ⟩
    Ω^-group k (Ptd-Trunc ⟨ k ⟩ (Ptd-Susp^ n X)) Trunc-level
      =⟨ π-Trunc-shift-iso k (Ptd-Susp^ n X) ⟩
    π k (Ptd-Susp^ n X) ∎

