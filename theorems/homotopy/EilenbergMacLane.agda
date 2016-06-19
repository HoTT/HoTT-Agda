{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.HSpace renaming (HSpaceStructure to HSS)
open import homotopy.Freudenthal
open import homotopy.IterSuspensionStable
open import homotopy.Pi2HSusp
open import homotopy.EM1HSpace

module homotopy.EilenbergMacLane where

-- EM(G,n) when G is π₁(A,a₀)
module EMImplicit {i} (A : Type i) (cA : is-connected 0 A)
  (gA : has-level 1 A) (A-H : HSS A) where

  private
    a₀ = HSS.e A-H
    X = ⊙[ A , a₀ ]

  ⊙EM : (n : ℕ) → Ptd i
  ⊙EM O = ⊙Ω X
  ⊙EM (S n) = ⊙Trunc ⟨ S n ⟩ (⊙Susp^ n X)

  module _ (n : ℕ) where
    EM = fst (⊙EM n)
    embase = snd (⊙EM n)

  EM-level : (n : ℕ) → has-level ⟨ n ⟩ (fst (⊙EM n))
  EM-level O = gA a₀ a₀
  EM-level (S n) = Trunc-level

  EM-conn : (n : ℕ) → is-connected ⟨ n ⟩ (EM (S n))
  EM-conn n = Trunc-preserves-conn ⟨ S n ⟩
                  (transport (λ t → is-connected t (fst (⊙Susp^ n X)))
                    (+2+0 ⟨ n ⟩₋₂) (⊙Susp^-conn n cA))

  {-
  π (S k) (EM (S n)) (embase (S n)) == π k (EM n) (embase n)
  where k > 0 and n = S (S n')
  -}
  module Stable (k n' : ℕ) (tk : k ≠ O) (tsk : S k ≠ O)
    (indexing : k ≤ S (S n'))
    where

    private
      n : ℕ
      n = S (S n')

      lte : ⟨ k ⟩ ≤T ⟨ n ⟩
      lte = ⟨⟩-monotone-≤ $ indexing

      kle : k ≤ (S n') *2
      kle = ≤-trans indexing (lemma n')
        where lemma : (n' : ℕ) → S (S n') ≤ (S n') *2
              lemma O = inl idp
              lemma (S n') = ≤-trans (≤-ap-S (lemma n')) (inr ltS)

    private
      module SS = Susp^Stable X cA (S n') k tk tsk kle

    abstract
      stable : π (S k) tsk (⊙EM (S n))
             == π k tk (⊙EM n)
      stable =
        π (S k) tsk (⊙EM (S n))
          =⟨ π-below-trunc _ tsk _ _ (≤T-ap-S lte) ⟩
        π (S k) tsk (⊙Susp^ n X)
          =⟨ SS.stable ⟩
        π k tk (⊙Susp^ (S n') X)
          =⟨ ! (π-below-trunc _ tk _ _ lte) ⟩
        π k tk (⊙EM n) ∎

  module BelowDiagonal where

    π₁ : (n : ℕ) (t1 : 1 ≠ 0 )
      → π 1 t1 (⊙EM (S (S n))) == Lift-Unit-Group
    π₁ n t1 =
      contr-is-0ᴳ (π 1 t1 (⊙EM (S (S n))))
        (connected-at-level-is-contr
          (raise-level-≤T (≤T-ap-S (≤T-ap-S (-2≤T ⟨ n ⟩₋₂)))
                          (Trunc-level {n = 0}))
          (Trunc-preserves-conn 0 (path-conn (EM-conn (S n)))))

    -- some clutter here arises from the definition of <;
    -- any simple way to avoid this?
    π-below : (k n : ℕ) (tk : k ≠ 0) → (k < n)
      → π k tk (⊙EM n) == Lift-Unit-Group
    π-below 0 _ tk lt = ⊥-rec (tk idp)
    π-below 1 .2 tk ltS = π₁ 0 tk
    π-below 1 .3 tk (ltSR ltS) = π₁ 1 tk
    π-below 1 (S (S n)) tk (ltSR (ltSR _)) = π₁ n tk
    π-below (S (S k)) ._ tssk ltS =
      Stable.stable (S k) k (ℕ-S≠O k) tssk (inr ltS)
      ∙ π-below (S k) _ (ℕ-S≠O k) ltS
    π-below (S (S k)) ._ tssk (ltSR ltS) =
      Stable.stable (S k) (S k) (ℕ-S≠O k) tssk (inr (ltSR ltS))
      ∙ π-below (S k) _ (ℕ-S≠O k) (ltSR ltS)
    π-below (S (S k)) ._ tssk (ltSR (ltSR ltS)) =
      Stable.stable (S k) (S (S k)) (ℕ-S≠O k) tssk (inr (ltSR (ltSR ltS)))
      ∙ π-below (S k) _ (ℕ-S≠O k) (ltSR (ltSR ltS))
    π-below (S (S k)) (S (S (S n))) tssk (ltSR (ltSR (ltSR lt))) =
      Stable.stable (S k) n (ℕ-S≠O k) tssk
        (inr (<-cancel-S (ltSR (ltSR (ltSR lt)))))
      ∙ π-below (S k) _ (ℕ-S≠O k) (<-cancel-S (ltSR (ltSR (ltSR lt))))


  module OnDiagonal where

    π₁ : (tn : 1 ≠ O) (t1 : 1 ≠ O)
      → π 1 tn (⊙EM 1) == π 1 t1 X
    π₁ tn t1 =
      π-below-trunc 1 tn 1 X ≤T-refl
      ∙ ap (λ t → π 1 t X)
           (prop-has-all-paths (Π-level (λ _ → ⊥-is-prop)) tn t1)

    private
      module Π₂ = Pi2HSusp A gA cA A-H

    π₂ : (tn : 2 ≠ O) (t1 : 1 ≠ O)
      → π 2 tn (⊙EM 2) == π 1 t1 X
    π₂ tn t1 =
      π-below-trunc 2 tn 2 (⊙Susp X) ≤T-refl
      ∙ Π₂.π₂-Suspension t1 tn

    π-diag : (n : ℕ) (tn : n ≠ 0) (t1 : 1 ≠ O)
      → π n tn (⊙EM n) == π 1 t1 X
    π-diag 0 tn _ = ⊥-rec (tn idp)
    π-diag 1 tn t1 = π₁ tn t1
    π-diag 2 tn t1 = π₂ tn t1
    π-diag (S (S (S n))) tn t1 =
      Stable.stable (S (S n)) n (ℕ-S≠O _) tn ≤-refl
      ∙ π-diag (S (S n)) (ℕ-S≠O _) t1

  module AboveDiagonal where

    π-above : (k n : ℕ) (tk : k ≠ 0) → (n < k)
      → π k tk (⊙EM n) == Lift-Unit-Group
    π-above k n tk lt =
      contr-is-0ᴳ (π k tk (⊙EM n))
        (inhab-prop-is-contr
          [ idp^ k ]
          (Trunc-preserves-level 0 (Ω^-level-in -1 k _
            (raise-level-≤T (lemma lt) (EM-level n)))))
      where lemma : {k n : ℕ} → n < k → ⟨ n ⟩ ≤T (⟨ k ⟩₋₂ +2+ -1)
            lemma ltS = inl (! (+2+-comm _ -1))
            lemma (ltSR lt) = ≤T-trans (lemma lt) (inr ltS)

  module Spectrum where

    private
      module Π₂ = Pi2HSusp A gA cA A-H

    spectrum0 : ⊙Ω (⊙EM 1) == ⊙EM 0
    spectrum0 =
      ⊙Ω (⊙EM 1)
        =⟨ ⊙ua (⊙≃-in (Trunc=-equiv _ _) idp) ⟩
      ⊙Trunc 0 (⊙Ω X)
        =⟨ ⊙ua (⊙≃-in (unTrunc-equiv _ (gA a₀ a₀)) idp) ⟩
      ⊙Ω X ∎

    spectrum1 : ⊙Ω (⊙EM 2) == ⊙EM 1
    spectrum1 =
      ⊙Ω (⊙EM 2)
        =⟨ ⊙ua (⊙≃-in (Trunc=-equiv _ _) idp) ⟩
      ⊙Trunc 1 (⊙Ω (⊙Susp X))
        =⟨ Π₂.⊙main-lemma ⟩
      X
        =⟨ ! (⊙ua (⊙≃-in (unTrunc-equiv _ gA) idp)) ⟩
      ⊙EM 1 ∎

    private
      sconn : (n : ℕ) → is-connected ⟨ S n ⟩ (fst (⊙Susp^ (S n) X))
      sconn n = transport (λ t → is-connected t (fst (⊙Susp^ (S n) X)))
                          (+2+0 ⟨ n ⟩₋₁) (⊙Susp^-conn (S n) cA)

      kle : (n : ℕ) → ⟨ S (S n) ⟩ ≤T ⟨ n ⟩ +2+ ⟨ n ⟩
      kle O = inl idp
      kle (S n) = ≤T-trans (≤T-ap-S (kle n))
                   (≤T-trans (inl (! (+2+-βr ⟨ n ⟩ ⟨ n ⟩)))
                               (inr ltS))

      module FS (n : ℕ) =
        FreudenthalEquiv ⟨ n ⟩₋₁ ⟨ S (S n) ⟩ (kle n)
          (fst (⊙Susp^ (S n) X)) (snd (⊙Susp^ (S n) X)) (sconn n)

    spectrumSS : (n : ℕ)
      → ⊙Ω (⊙EM (S (S (S n)))) == ⊙EM (S (S n))
    spectrumSS n =
      ⊙Ω (⊙EM (S (S (S n))))
        =⟨ ⊙ua (⊙≃-in (Trunc=-equiv _ _) idp) ⟩
      ⊙Trunc ⟨ S (S n) ⟩ (⊙Ω (⊙Susp^ (S (S n)) X))
        =⟨ ! (FS.⊙path n) ⟩
      ⊙EM (S (S n)) ∎

    abstract
      spectrum : (n : ℕ) → ⊙Ω (⊙EM (S n)) == ⊙EM n
      spectrum 0 = spectrum0
      spectrum 1 = spectrum1
      spectrum (S (S n)) = spectrumSS n

module EMExplicit {i} (G : Group i) (G-abelian : is-abelian G) where
  module K₁ = EM₁ G
  module HSpace = EM₁HSpace G G-abelian
  open EMImplicit K₁.EM₁ K₁.EM₁-conn K₁.emlevel HSpace.H-EM₁ public

  open BelowDiagonal public using (π-below)

  π-diag : (n : ℕ) (tn : n ≠ 0) → π n tn (⊙EM n) == G
  π-diag n tn =
    OnDiagonal.π-diag n tn (ℕ-S≠O 0) ∙ K₁.π₁.π₁-iso

  open AboveDiagonal public using (π-above)
  open Spectrum public using (spectrum)
