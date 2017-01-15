{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.Freudenthal

module homotopy.IterSuspensionStable where

{- π (S k) (Ptd-Susp^ (S n) X) == π k (Ptd-Susp^ n X), where k = S k'
   Susp^Stable below assumes k ≠ O instead of taking k' as the argument -}
module Susp^StableSucc {i} (X : Ptd i) (cX : is-connected 0 (fst X))
  (k n : ℕ) (Skle : S k ≤ n *2) where

  {- some numeric computations -}
  private
    Skle' : ⟨ S k ⟩ ≤T ⟨ n ⟩₋₁ +2+ ⟨ n ⟩₋₁
    Skle' = ≤T-trans (⟨⟩-monotone-≤ Skle) (inl (lemma n))
      where lemma : (n : ℕ) → ⟨ n *2 ⟩ == ⟨ n ⟩₋₁ +2+ ⟨ n ⟩₋₁
            lemma O = idp
            lemma (S n') = ap S (ap S (lemma n')
                                 ∙ ! (+2+-βr ⟨ S n' ⟩₋₂ ⟨ S n' ⟩₋₂))

  private
    module F = FreudenthalIso
      ⟨ n ⟩₋₂ k Skle' (⊙Susp^ n X)
      (transport (λ t → is-connected t (fst (⊙Susp^ n X)))
                 (+2+0 ⟨ n ⟩₋₂) (⊙Susp^-conn n cX))

  stable : πS (S k) (⊙Susp^ (S n) X) ≃ᴳ πS k (⊙Susp^ n X)
  stable =
    πS (S k) (⊙Susp^ (S n) X)
      ≃ᴳ⟨ πS-Ω-split-iso k (⊙Susp^ (S n) X) ⟩
    πS k (⊙Ω (⊙Susp^ (S n) X))
      ≃ᴳ⟨ Ω^S-group-Trunc-fuse-diag-iso k (⊙Ω (⊙Susp^ (S n) X)) ⁻¹ᴳ ⟩
    Ω^S-group k (⊙Trunc ⟨ S k ⟩ (⊙Ω (⊙Susp^ (S n) X))) Trunc-level
      ≃ᴳ⟨ F.iso ⁻¹ᴳ ⟩
    Ω^S-group k (⊙Trunc ⟨ S k ⟩ (⊙Susp^ n X)) Trunc-level
      ≃ᴳ⟨ Ω^S-group-Trunc-fuse-diag-iso k (⊙Susp^ n X) ⟩
    πS k (⊙Susp^ n X) ≃ᴳ∎
