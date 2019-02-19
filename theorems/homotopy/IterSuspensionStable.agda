{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.Freudenthal

module homotopy.IterSuspensionStable where

{- π (S k) (Ptd-Susp^ (S n) X) == π k (Ptd-Susp^ n X), where k = S k'
   Susp^Stable below assumes k ≠ O instead of taking k' as the argument -}
module Susp^StableSucc {i} (k n : ℕ) (Skle : S k ≤ n *2)
  (X : Ptd i) {{_ : is-connected ⟨ n ⟩ (de⊙ X)}} where

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
      ⟨ n ⟩₋₂ k Skle' X

  stable : πS (S k) (⊙Susp (de⊙ X)) ≃ᴳ πS k X
  stable =
    πS (S k) (⊙Susp (de⊙ X))
      ≃ᴳ⟨ πS-Ω-split-iso k (⊙Susp (de⊙ X)) ⟩
    πS k (⊙Ω (⊙Susp (de⊙ X)))
      ≃ᴳ⟨ Ω^S-group-Trunc-fuse-diag-iso k (⊙Ω (⊙Susp (de⊙ X))) ⁻¹ᴳ ⟩
    Ω^S-group k (⊙Trunc ⟨ S k ⟩ (⊙Ω (⊙Susp (de⊙ X))))
      ≃ᴳ⟨ F.iso ⁻¹ᴳ ⟩
    Ω^S-group k (⊙Trunc ⟨ S k ⟩ X)
      ≃ᴳ⟨ Ω^S-group-Trunc-fuse-diag-iso k X ⟩
    πS k X ≃ᴳ∎
