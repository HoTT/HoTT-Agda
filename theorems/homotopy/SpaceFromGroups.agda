{-# OPTIONS --without-K #-}

open import HoTT
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

  πS-X : (n : ℕ) → πS n X == πS n (F n)
  πS-X n =
    prefix-lemma n O F pF
    ∙ ap (πS n) (! (⊙ua (⊙fin-tuples-cons (λ k → F (n + k)))))
    ∙ πS-× n (F (n + O)) (⊙FinTuples (λ k → F (n + S k)))
    ∙ ap (λ H → πS n (F (n + O)) ×ᴳ H)
         (contr-is-0ᴳ _ $
           connected-at-level-is-contr (Trunc-level {n = 0}) $
             Trunc-preserves-conn 0 $ Ω^-conn-in _ (S n) _ $
               transport
                 (λ k → is-connected k
                          (fst (⊙FinTuples (λ k → F (n + S k)))))
                 (+2+-comm 0 ⟨ n ⟩₋₁)
                 (ncolim-conn _ _ $ connected-lemma _ _ $ λ k →
                   transport (λ s → is-connected ⟨ s ⟩ (fst (F (n + S k))))
                     (+-βr n k ∙ +-comm (S n) k)
                     (cF (n + S k))))
    ∙ ×ᴳ-unit-r
    ∙ ap (λ k → πS n (F k)) (+-unit-r n)

    where
    {- In computing πₙ₊₁, spaces before Fₙ are ignored because of their
     - truncation level -}
    prefix-lemma : (n : ℕ) (m : ℕ) (F : ℕ → Ptd i)
      (pF : (k : ℕ) → has-level ⟨ S m + k ⟩ (fst (F k)))
      → πS (m + n) (⊙FinTuples F)
        == πS (m + n) (⊙FinTuples (λ k → F (n + k)))
    prefix-lemma O m F pF = idp
    prefix-lemma (S n) m F pF =
      ap (πS (m + S n)) (! (⊙ua (⊙fin-tuples-cons F)))
      ∙ πS-× (m + S n) (F O) (⊙FinTuples (F ∘ S))
      ∙ ap2 _×ᴳ_ lemma₁ lemma₂
      ∙ ×ᴳ-unit-l
      where
      {- ignore first space -}
      lemma₁ : πS (m + S n) (F O) == 0ᴳ
      lemma₁ =
        πS-above-level (m + S n) _ (F O)
          (⟨⟩-monotone-< (<-ap-S (<-+-l m (O<S n)))) (pF O)

      {- ignore the rest by recursive call -}
      lemma₂ : πS (m + S n) (⊙FinTuples (F ∘ S))
        == πS (m + S n) (⊙FinTuples (λ k → F (S (n + k))))
      lemma₂ =
        transport (λ s → πS s (⊙FinTuples (F ∘ S))
                      == πS s (⊙FinTuples (λ k → F (S n + k))))
          (! (+-βr m n))
          (prefix-lemma n (S m) (F ∘ S)
            (λ k → transport (λ s → has-level ⟨ s ⟩ (fst (F (S k))))
                     (+-βr (S m) k)
                     (pF (S k))))


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
  (abG : (n : ℕ) → is-abelian (G (S n))) where

  private
    F : ℕ → Ptd i
    F O = EM₁.⊙EM₁ (G O)
    F (S n) = EMExplicit.⊙EM (G (S n)) (abG n) (S (S n))

    pF : (n : ℕ) → has-level ⟨ S n ⟩ (fst (F n))
    pF O = EM₁.emlevel (G O)
    pF (S n) = EMExplicit.EM-level (G (S n)) (abG n) (S (S n))

    cF : (n : ℕ) → is-connected ⟨ n ⟩ (fst (F n))
    cF O = EM₁.EM₁-conn (G O)
    cF (S n) = EMExplicit.EM-conn (G (S n)) (abG n) (S n)

    module M = SpaceFromEMs F pF cF

  X = M.X

  πS-X : (n : ℕ) → πS n X == G n
  πS-X O = M.πS-X O ∙ EM₁.π₁.π₁-iso (G O)
  πS-X (S n) =
    M.πS-X (S n) ∙ EMExplicit.πS-diag (G (S n)) (abG n) (S n)
