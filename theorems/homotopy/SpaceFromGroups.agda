{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane1
open import homotopy.EilenbergMacLane

{- Given sequence of groups (Gₙ : n ≥ 1) such that Gₙ is abelian for n > 1,
 - we can construct a space X such that πₙ(X) == Gₙ.
 - (We can also make π₀(X) whatever we want but this isn't done here.) -}

module homotopy.SpaceFromGroups where

{- From a sequence of spaces (Fₙ) such that Fₙ is n-connected and
 - n+1-truncated, construct a space X such that πₙ₊₁(X) == πₙ₊₁(Fₙ) -}
module SpaceFromEMs {i} (F : ℕ → Ptd i)
  (pF : (n : ℕ) → has-level ⟨ S n ⟩ (fst (F n)))
  (cF : (n : ℕ) → is-connected ⟨ n ⟩ (fst (F n))) where

  X : Ptd i
  X = ⊙FinTuples F

  πS-X : (n : ℕ) → πS n X ≃ᴳ πS n (F n)
  πS-X n =
    πS n (⊙FinTuples F)
      ≃ᴳ⟨ prefix-lemma n O F pF ⟩
    πS n (⊙FinTuples (λ k → F (n + k)))
      ≃ᴳ⟨ πS-emap n (⊙fin-tuples-cons (λ k → F (n + k))) ⁻¹ᴳ ⟩
    πS n (F (n + O) ⊙× ⊙FinTuples (λ k → F (n + S k)))
      ≃ᴳ⟨ πS-× n (F (n + O)) (⊙FinTuples (λ k → F (n + S k))) ⟩
    πS n (F (n + O)) ×ᴳ πS n (⊙FinTuples (λ k → F (n + S k)))
      ≃ᴳ⟨ ×ᴳ-emap (idiso (πS n (F (n + O))) )
         (contr-iso-0ᴳ _ $
           connected-at-level-is-contr (Trunc-level {n = 0}) $
             Trunc-preserves-conn 0 $ Ω^-conn _ (S n) _ $
               transport
                 (λ k → is-connected k
                          (fst (⊙FinTuples (λ k → F (n + S k)))))
                 (+2+-comm 0 ⟨ n ⟩₋₁)
                 (ncolim-conn _ _ $ connected-lemma _ _ $ λ k →
                   transport (λ s → is-connected ⟨ s ⟩ (fst (F (n + S k))))
                     (+-βr n k ∙ +-comm (S n) k)
                     (cF (n + S k)))) ⟩
    πS n (F (n + O)) ×ᴳ 0ᴳ
      ≃ᴳ⟨ ×ᴳ-unit-r _ ⟩
    πS n (F (n + O))
      ≃ᴳ⟨ transportᴳ-equiv (λ k → πS n (F k)) (+-unit-r n) ⟩
    πS n (F n)
      ≃ᴳ∎
    where
    {- In computing πₙ₊₁, spaces before Fₙ are ignored because of their
     - truncation level -}
    prefix-lemma : (n : ℕ) (m : ℕ) (F : ℕ → Ptd i)
      (pF : (k : ℕ) → has-level ⟨ S m + k ⟩ (fst (F k)))
      → πS (m + n) (⊙FinTuples F)
        ≃ᴳ πS (m + n) (⊙FinTuples (λ k → F (n + k)))
    prefix-lemma O m F pF = idiso _
    prefix-lemma (S n) m F pF =
      πS (m + S n) (⊙FinTuples F)
        ≃ᴳ⟨ πS-emap (m + S n) (⊙fin-tuples-cons F) ⁻¹ᴳ ⟩
      πS (m + S n) (F O ⊙× ⊙FinTuples (F ∘ S))
        ≃ᴳ⟨ πS-× (m + S n) (F O) (⊙FinTuples (F ∘ S)) ⟩
      πS (m + S n) (F O) ×ᴳ πS (m + S n) (⊙FinTuples (F ∘ S))
        ≃ᴳ⟨ ×ᴳ-emap lemma₁ lemma₂ ⟩
      0ᴳ ×ᴳ πS (m + S n) (⊙FinTuples (λ k → F (S (n + k))))
        ≃ᴳ⟨ ×ᴳ-unit-l _ ⟩
      πS (m + S n) (⊙FinTuples (λ k → F (S (n + k))))
        ≃ᴳ∎
      where
      {- ignore first space -}
      lemma₁ : πS (m + S n) (F O) ≃ᴳ 0ᴳ
      lemma₁ =
        πS->level-econv (m + S n) _ (F O)
          (⟨⟩-monotone-< (<-ap-S (<-+-l m (O<S n)))) (pF O)

      {- ignore the rest by recursive call -}
      lemma₂ : πS (m + S n) (⊙FinTuples (F ∘ S))
        ≃ᴳ πS (m + S n) (⊙FinTuples (λ k → F (S (n + k))))
      lemma₂ =
        πS (m + S n) (⊙FinTuples (F ∘ S))
          ≃ᴳ⟨ transportᴳ-equiv (λ s → πS s (⊙FinTuples (F ∘ S))) (+-βr m n) ⟩
        πS (S m + n) (⊙FinTuples (F ∘ S))
          ≃ᴳ⟨ prefix-lemma n (S m) (F ∘ S)
                (λ k → transport (λ s → has-level ⟨ s ⟩ (fst (F (S k))))
                     (+-βr (S m) k)
                     (pF (S k))) ⟩
        πS (S m + n) (⊙FinTuples (λ k → F (S (n + k))))
          ≃ᴳ⟨ transportᴳ-equiv (λ s → πS s (⊙FinTuples (λ k → F (S (n + k))))) (+-βr m n) ⁻¹ᴳ ⟩
        πS (m + S n) (⊙FinTuples (λ k → F (S (n + k))))
          ≃ᴳ∎

    connected-lemma : (m : ℕ) (F : ℕ → Ptd i)
      (cA' : (n : ℕ) → is-connected ⟨ n + m ⟩ (fst (F n)))
      (n : ℕ) → is-connected ⟨ m ⟩ (fst (FinTuplesType F n))
    connected-lemma m F cA' O =
      Trunc-preserves-level ⟨ m ⟩ (Lift-level Unit-is-contr)
    connected-lemma m F cA' (S n) = ×-conn
      (cA' O)
      (connected-lemma m (F ∘ S)
        (λ n → connected-≤T (⟨⟩-monotone-≤ (inr ltS)) (cA' (S n))) n)

{- Given sequence of groups (Gₙ : n ≥ 1) such that Gₙ is abelian for n > 1,
 - construct a space X such that πₙ(X) == Gₙ. -}
module SpaceFromGroups {i} (G : ℕ → Group i)
  (abG-S : (n : ℕ) → is-abelian (G (S n))) where

  private
    F : ℕ → Ptd i
    F O = ⊙EM₁ (G O)
    F (S n) = EMExplicit.⊙EM (G (S n) , abG-S n) (S (S n))

    pF : (n : ℕ) → has-level ⟨ S n ⟩ (fst (F n))
    pF O = EM₁-level {G = G O}
    pF (S n) = EMExplicit.EM-level (G (S n) , abG-S n) (S (S n))

    cF : (n : ℕ) → is-connected ⟨ n ⟩ (fst (F n))
    cF O = EM₁-conn {G = G O}
    cF (S n) = EMExplicit.EM-conn (G (S n) , abG-S n) (S n)

    module M = SpaceFromEMs F pF cF

  X = M.X

  πS-X : (n : ℕ) → πS n X ≃ᴳ G n
  πS-X O = π₁-EM₁ (G O) ∘eᴳ M.πS-X O
  πS-X (S n) =
    EMExplicit.πS-diag (G (S n) , abG-S n) (S n) ∘eᴳ M.πS-X (S n)
