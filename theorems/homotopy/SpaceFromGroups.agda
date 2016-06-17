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

  πₙ : (n : ℕ) → π (S n) (ℕ-S≠O _) X == π (S n) (ℕ-S≠O _) (F n)
  πₙ n =
    prefix-lemma n O F pF
    ∙ ap (π (S n) (ℕ-S≠O _)) (! (⊙ua (⊙fin-tuples-cons (λ k → F (n + k)))))
    ∙ π-× (S n) (ℕ-S≠O _) (F (n + O)) (⊙FinTuples (λ k → F (n + S k)))
    ∙ ap (λ H → π (S n) (ℕ-S≠O _) (F (n + O)) ×ᴳ H)
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
    ∙ ap (λ k → π (S n) (ℕ-S≠O _) (F k)) (+-unit-r n)

    where
    {- In computing πₙ₊₁, spaces before Fₙ are ignored because of their
     - truncation level -}
    prefix-lemma : (n : ℕ) (m : ℕ) (F : ℕ → Ptd i)
      (pF : (k : ℕ) → has-level ⟨ S m + k ⟩ (fst (F k)))
      → π (S m + n) (ℕ-S≠O _) (⊙FinTuples F)
        == π (S m + n) (ℕ-S≠O _) (⊙FinTuples (λ k → F (n + k)))
    prefix-lemma O m F pF = idp
    prefix-lemma (S n) m F pF =
      ap (π (S m + S n) (ℕ-S≠O _)) (! (⊙ua (⊙fin-tuples-cons F)))
      ∙ π-× (S m + S n) (ℕ-S≠O _) (F O) (⊙FinTuples (F ∘ S))
      ∙ ap2 _×ᴳ_ lemma₁ lemma₂
      ∙ ×ᴳ-unit-l
      where
      {- ignore first space -}
      lemma₁ : π (S (m + S n)) (ℕ-S≠O _) (F O) == 0ᴳ
      lemma₁ =
        π-above-level (S (m + S n)) (ℕ-S≠O _) _ (F O)
          (⟨⟩-monotone-< (<-ap-S (<-+-l m (O<S n)))) (pF O)

      {- ignore the rest by recursive call -}
      lemma₂ : π (S (m + S n)) (ℕ-S≠O _) (⊙FinTuples (F ∘ S))
        == π (S (m + S n)) (ℕ-S≠O (m + S n)) (⊙FinTuples (λ k → F (S (n + k))))
      lemma₂ =
        transport (λ s → π (S s) (ℕ-S≠O s) (⊙FinTuples (F ∘ S))
                      == π (S s) (ℕ-S≠O s) (⊙FinTuples (λ k → F (S n + k))))
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

  πₙ : (n : ℕ) → π (S n) (ℕ-S≠O _) X == G n
  πₙ O = M.πₙ O ∙ EM₁.π₁.π₁-iso (G O)
  πₙ (S n) =
    M.πₙ (S n) ∙ EMExplicit.π-diag (G (S n)) (abG n) (S (S n)) (ℕ-S≠O _)
