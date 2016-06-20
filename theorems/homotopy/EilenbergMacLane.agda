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
  module Stable (k n : ℕ) (indexing : S k ≤ S (S n))
    where

    private
      SSn : ℕ
      SSn = S (S n)

      lte : ⟨ S k ⟩ ≤T ⟨ SSn ⟩
      lte = ⟨⟩-monotone-≤ $ indexing

      Skle : S k ≤ (S n) *2
      Skle = ≤-trans indexing (lemma n)
        where lemma : (n' : ℕ) → S (S n') ≤ (S n') *2
              lemma O = inl idp
              lemma (S n') = ≤-trans (≤-ap-S (lemma n')) (inr ltS)

    private
      module SS = Susp^StableSucc X cA (S n) k Skle

    abstract
      stable : πS (S k) (⊙EM (S SSn))
             == πS k (⊙EM SSn)
      stable =
        πS (S k) (⊙EM (S SSn))
          =⟨ πS-below-trunc _ _ _ (≤T-ap-S lte) ⟩
        πS (S k) (⊙Susp^ SSn X)
          =⟨ SS.stable ⟩
        πS k (⊙Susp^ (S n) X)
          =⟨ ! (πS-below-trunc _ _ _ lte) ⟩
        πS k (⊙EM SSn) ∎

  module BelowDiagonal where

    π₁ : (n : ℕ) → πS 0 (⊙EM (S (S n))) == Lift-Unit-group
    π₁ n =
      contr-is-0ᴳ (πS 0 (⊙EM (S (S n))))
        (connected-at-level-is-contr
          (raise-level-≤T (≤T-ap-S (≤T-ap-S (-2≤T ⟨ n ⟩₋₂)))
                          (Trunc-level {n = 0}))
          (Trunc-preserves-conn 0 (path-conn (EM-conn (S n)))))

    -- some clutter here arises from the definition of <;
    -- any simple way to avoid this?
    πS-below : (k n : ℕ) → (S k < n)
      → πS k (⊙EM n) == Lift-Unit-group
    πS-below 0 .2 ltS = π₁ 0
    πS-below 0 .3 (ltSR ltS) = π₁ 1
    πS-below 0 (S (S n)) (ltSR (ltSR _)) = π₁ n
    πS-below (S k) ._ ltS =
      Stable.stable k k (inr ltS)
      ∙ πS-below k _ ltS
    πS-below (S k) ._ (ltSR ltS) =
      Stable.stable k (S k) (inr (ltSR ltS))
      ∙ πS-below k _ (ltSR ltS)
    πS-below (S k) ._ (ltSR (ltSR ltS)) =
      Stable.stable k (S (S k)) (inr (ltSR (ltSR ltS)))
      ∙ πS-below k _ (ltSR (ltSR ltS))
    πS-below (S k) (S (S (S n))) (ltSR (ltSR (ltSR lt))) =
      Stable.stable k n
        (inr (<-cancel-S (ltSR (ltSR (ltSR lt)))))
      ∙ πS-below k _ (<-cancel-S (ltSR (ltSR (ltSR lt))))


  module OnDiagonal where

    π₁ : πS 0 (⊙EM 1) == πS 0 X
    π₁ = πS-below-trunc 0 1 X ≤T-refl

    private
      module Π₂ = Pi2HSusp A gA cA A-H

    π₂ : πS 1 (⊙EM 2) == πS 0 X
    π₂ =
      πS-below-trunc 1 2 (⊙Susp X) ≤T-refl
      ∙ Π₂.π₂-Suspension

    πS-diag : (n : ℕ) → πS n (⊙EM (S n)) == πS 0 X
    πS-diag 0 = π₁
    πS-diag 1 = π₂
    πS-diag (S (S n)) =
      Stable.stable (S n) n ≤-refl
      ∙ πS-diag (S n)

  module AboveDiagonal where

    πS-above : (k n : ℕ) → (n < S k)
      → πS k (⊙EM n) == Lift-Unit-group
    πS-above k n lt =
      contr-is-0ᴳ (πS k (⊙EM n))
        (inhab-prop-is-contr
          [ idp^ (S k) ]
          (Trunc-preserves-level 0 (Ω^-level-in -1 (S k) _
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

  open BelowDiagonal public using (πS-below)

  πS-diag : (n : ℕ) → πS n (⊙EM (S n)) == G
  πS-diag n = OnDiagonal.πS-diag n ∙ K₁.π₁.π₁-iso

  open AboveDiagonal public using (πS-above)
  open Spectrum public using (spectrum)
