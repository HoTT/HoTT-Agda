{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.Freudenthal

module homotopy.IteratedSuspension where

Ptd-Susp^ : ∀ {i} (n : ℕ) → Ptd i → Ptd i
Ptd-Susp^ O X = X
Ptd-Susp^ (S n) X = Ptd-Susp (Ptd-Susp^ n X)

Ptd-Susp^-conn : ∀ {i} (n : ℕ) {X : Ptd i} {m : ℕ₋₂}
  → is-connected m (fst X) → is-connected ((n -2) +2+ m) (fst (Ptd-Susp^ n X))
Ptd-Susp^-conn O cX = cX
Ptd-Susp^-conn (S n) cX = Susp-conn (Ptd-Susp^-conn n cX)

{- π (S k) (Ptd-Susp^ (S n) X) == π k (Ptd-Susp^ n X), where k = S k' 
   Susp^Stable below uses instance arguments instead of proving for S k' -}
module Susp^StableSucc {i} (X : Ptd i) (cX : is-connected ⟨0⟩ (fst X))
  (n : ℕ) (k' : ℕ) (kle : S k' ≤ n *2) where
  
  {- need k,n ≥ 1 -}
  k : ℕ
  k = S k'

  {- some numeric computations -}
  private
    kle' : ⟨ k ⟩ ≤T S ((n -2) +2+ S (n -2))
    kle' = ≤T-trans (⟨⟩-monotone-≤ kle) (inl (lemma n))
      where lemma : (n : ℕ) → ⟨ n *2 ⟩ == S ((n -2) +2+ S (n -2))
            lemma O = idp
            lemma (S n') = ap S (ap S (lemma n') 
                                 ∙ ! (+2+-βr (S n' -2) (S n' -2)))


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

  stable : ⦃ pk : k ≠ 0 ⦄ ⦃ psk : S k ≠ 0 ⦄
    → π (S k) ⦃ psk ⦄ (Ptd-Susp^ (S n) X) == π k ⦃ pk ⦄ (Ptd-Susp^ n X)
  stable ⦃ pk ⦄ ⦃ psk ⦄ = 
    π (S k) ⦃ psk ⦄ (Ptd-Susp^ (S n) X)
      =⟨ π-inner-iso k ⦃ pk ⦄ ⦃ psk ⦄ (Ptd-Susp^ (S n) X) ⟩
    π k ⦃ pk ⦄ (Ptd-Ω (Ptd-Susp^ (S n) X)) 
      =⟨ ! (π-Trunc-shift-iso k ⦃ pk ⦄ (Ptd-Ω (Ptd-Susp^ (S n) X))) ⟩
    Ω^-group k ⦃ pk ⦄ (Ptd-Trunc ⟨ k ⟩ (Ptd-Ω (Ptd-Susp^ (S n) X))) Trunc-level
      =⟨ ! F.iso ⟩
    Ω^-group k ⦃ pk ⦄ (Ptd-Trunc ⟨ k ⟩ (Ptd-Susp^ n X)) Trunc-level
      =⟨ π-Trunc-shift-iso k ⦃ pk ⦄ (Ptd-Susp^ n X) ⟩
    π k ⦃ pk ⦄ (Ptd-Susp^ n X) ∎

{- π (S k) (Ptd-Susp^ (S n) X) == π k (Ptd-Susp^ n X), where k > 0 -}
module Susp^Stable {i} (X : Ptd i) (cX : is-connected ⟨0⟩ (fst X))
  (n : ℕ) (k : ℕ) ⦃ pk : k ≠ 0 ⦄ ⦃ psk : S k ≠ 0 ⦄ (kle : k ≤ n *2) where

  private
    lemma : ∀ {i} (C : (n : ℕ) ⦃ _ : n ≠ 0 ⦄ ⦃ _ : S n ≠ 0 ⦄ → Type i) 
      → ((n : ℕ) ⦃ psn : S n ≠ 0 ⦄ ⦃ pssn : S (S n) ≠ 0 ⦄ 
            → C (S n) ⦃ psn ⦄ ⦃ pssn ⦄)
      → ((n : ℕ) ⦃ pn : n ≠ 0 ⦄ ⦃ psn : S n ≠ 0 ⦄
            → C n ⦃ pn ⦄ ⦃ psn ⦄)
    lemma C f O ⦃ posi ⦄ ⦃ _ ⦄ = ⊥-rec (posi idp)
    lemma C f (S n) ⦃ psn ⦄ ⦃ pssn ⦄ = f n ⦃ psn ⦄ ⦃ pssn ⦄

  abstract
    stable : π (S k) ⦃ psk ⦄ (Ptd-Susp^ (S n) X) == π k ⦃ pk ⦄ (Ptd-Susp^ n X)
    stable = lemma
      (λ r → λ ⦃ pr ⦄ → λ ⦃ psr ⦄ → (r ≤ n *2) → 
         π (S r) ⦃ psr ⦄ (Ptd-Susp^ (S n) X) == π r ⦃ pr ⦄ (Ptd-Susp^ n X))
      (λ r' → λ ⦃ psr' ⦄ → λ ⦃ pssr' ⦄ → λ rle → 
        Susp^StableSucc.stable X cX n r' rle ⦃ psr' ⦄ ⦃ pssr' ⦄)
      k ⦃ pk ⦄ ⦃ psk ⦄ kle
