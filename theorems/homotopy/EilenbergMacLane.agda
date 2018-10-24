{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.HSpace renaming (HSpaceStructure to HSS)
open import homotopy.Freudenthal
open import homotopy.IterSuspensionStable
import homotopy.Pi2HSusp as Pi2HSusp
open import homotopy.EM1HSpace
open import homotopy.EilenbergMacLane1

module homotopy.EilenbergMacLane where

-- EM(G,n) when G is π₁(A,a₀)
module EMImplicit {i} {X : Ptd i} {{_ : is-connected 0 (de⊙ X)}}
  {{X-level : has-level 1 (de⊙ X)}} (H-X : HSS X) where

  private
    A = de⊙ X
    a₀ = pt X

  ⊙EM : (n : ℕ) → Ptd i
  ⊙EM O = ⊙Ω X
  ⊙EM (S n) = ⊙Trunc ⟨ S n ⟩ (⊙Susp^ n X)

  module _ (n : ℕ) where
    EM = de⊙ (⊙EM n)

  EM-level : (n : ℕ) → has-level ⟨ n ⟩ (EM n)
  EM-level O = has-level-apply X-level _ _
  EM-level (S n) = Trunc-level

  instance
    EM-conn : (n : ℕ) → is-connected ⟨ n ⟩ (EM (S n))
    EM-conn n = Trunc-preserves-conn (⊙Susp^-conn' n)

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
      module SS = Susp^StableSucc k (S n) Skle (⊙Susp^ (S n) X) {{⊙Susp^-conn' (S n)}}

    abstract
      stable : πS (S k) (⊙EM (S SSn)) ≃ᴳ πS k (⊙EM SSn)
      stable =
        πS (S k) (⊙EM (S SSn))
          ≃ᴳ⟨ πS-Trunc-fuse-≤-iso _ _ _ (≤T-ap-S lte) ⟩
        πS (S k) (⊙Susp^ SSn X)
          ≃ᴳ⟨ SS.stable ⟩
        πS k (⊙Susp^ (S n) X)
          ≃ᴳ⟨ πS-Trunc-fuse-≤-iso _ _ _ lte ⁻¹ᴳ ⟩
        πS k (⊙EM SSn)
          ≃ᴳ∎

  module BelowDiagonal where

    π₁ : (n : ℕ) → πS 0 (⊙EM (S (S n))) ≃ᴳ 0ᴳ
    π₁ n =
      contr-iso-0ᴳ (πS 0 (⊙EM (S (S n))))
        (connected-at-level-is-contr
          {{raise-level-≤T (≤T-ap-S (≤T-ap-S (-2≤T ⟨ n ⟩₋₂)))
                          (Trunc-level {n = 0})}})

    -- some clutter here arises from the definition of <;
    -- any simple way to avoid this?
    πS-below : (k n : ℕ) → (S k < n)
      → πS k (⊙EM n) ≃ᴳ 0ᴳ
    πS-below 0 .2 ltS = π₁ 0
    πS-below 0 .3 (ltSR ltS) = π₁ 1
    πS-below 0 (S (S n)) (ltSR (ltSR _)) = π₁ n
    πS-below (S k) ._ ltS =
      πS-below k _ ltS
      ∘eᴳ Stable.stable k k (inr ltS)
    πS-below (S k) ._ (ltSR ltS) =
      πS-below k _ (ltSR ltS)
      ∘eᴳ Stable.stable k (S k) (inr (ltSR ltS))
    πS-below (S k) ._ (ltSR (ltSR ltS)) =
      πS-below k _ (ltSR (ltSR ltS))
      ∘eᴳ Stable.stable k (S (S k)) (inr (ltSR (ltSR ltS)))
    πS-below (S k) (S (S (S n))) (ltSR (ltSR (ltSR lt))) =
      πS-below k _ (<-cancel-S (ltSR (ltSR (ltSR lt))))
      ∘eᴳ Stable.stable k n (inr (<-cancel-S (ltSR (ltSR (ltSR lt)))))


  module OnDiagonal where

    π₁ : πS 0 (⊙EM 1) ≃ᴳ πS 0 X
    π₁ = πS-Trunc-fuse-≤-iso 0 1 X ≤T-refl

    private
      module Π₂ = Pi2HSusp H-X

    π₂ : πS 1 (⊙EM 2) ≃ᴳ πS 0 X
    π₂ = Π₂.π₂-Susp
     ∘eᴳ πS-Trunc-fuse-≤-iso 1 2 (⊙Susp (de⊙ X)) ≤T-refl

    πS-diag : (n : ℕ) → πS n (⊙EM (S n)) ≃ᴳ πS 0 X
    πS-diag 0 = π₁
    πS-diag 1 = π₂
    πS-diag (S (S n)) = πS-diag (S n)
                    ∘eᴳ Stable.stable (S n) n ≤-refl

  module AboveDiagonal where

    πS-above : ∀ (k n : ℕ) → (n < S k)
      → πS k (⊙EM n) ≃ᴳ 0ᴳ
    πS-above k n lt =
      contr-iso-0ᴳ (πS k (⊙EM n))
        (inhab-prop-is-contr
          [ idp^ (S k) ]
          {{Trunc-preserves-level 0 (Ω^-level -1 (S k) _
            (raise-level-≤T (lemma lt) (EM-level n)))}})
      where lemma : {k n : ℕ} → n < k → ⟨ n ⟩ ≤T (⟨ k ⟩₋₂ +2+ -1)
            lemma ltS = inl (! (+2+-comm _ -1))
            lemma (ltSR lt) = ≤T-trans (lemma lt) (inr ltS)

  module Spectrum where

    private
      module Π₂ = Pi2HSusp H-X

    spectrum0 : ⊙Ω (⊙EM 1) ⊙≃ ⊙EM 0
    spectrum0 =
      ⊙Ω (⊙EM 1)
        ⊙≃⟨ ≃-to-⊙≃ (=ₜ-equiv _ _) idp ⟩
      ⊙Trunc 0 (⊙Ω X)
        ⊙≃⟨ ≃-to-⊙≃ (unTrunc-equiv _) idp ⟩
      ⊙Ω X ⊙≃∎

    spectrum1 : ⊙Ω (⊙EM 2) ⊙≃ ⊙EM 1
    spectrum1 =
      ⊙Ω (⊙EM 2)
        ⊙≃⟨ ≃-to-⊙≃ (=ₜ-equiv _ _) idp ⟩
      ⊙Trunc 1 (⊙Ω (⊙Susp (de⊙ X)))
        ⊙≃⟨ Π₂.⊙eq ⟩
      ⊙EM 1 ⊙≃∎

    private
      instance
        sconn : (n : ℕ) → is-connected ⟨ S n ⟩ (de⊙ (⊙Susp^ (S n) X))
        sconn n = ⊙Susp^-conn' (S n)

      kle : (n : ℕ) → ⟨ S (S n) ⟩ ≤T ⟨ n ⟩ +2+ ⟨ n ⟩
      kle O = inl idp
      kle (S n) = ≤T-trans (≤T-ap-S (kle n))
                   (≤T-trans (inl (! (+2+-βr ⟨ n ⟩ ⟨ n ⟩)))
                               (inr ltS))

      module FS (n : ℕ) =
        FreudenthalEquiv ⟨ n ⟩₋₁ ⟨ S (S n) ⟩ (kle n)
          (⊙Susp^ (S n) X)

    spectrumSS : (n : ℕ)
      → ⊙Ω (⊙EM (S (S (S n)))) ⊙≃ ⊙EM (S (S n))
    spectrumSS n =
      ⊙Ω (⊙EM (S (S (S n))))
        ⊙≃⟨ ≃-to-⊙≃ (=ₜ-equiv _ _) idp ⟩
      ⊙Trunc ⟨ S (S n) ⟩ (⊙Ω (⊙Susp^ (S (S n)) X))
        ⊙≃⟨ FS.⊙eq n ⊙⁻¹ ⟩
      ⊙EM (S (S n)) ⊙≃∎

    abstract
      spectrum : (n : ℕ) → ⊙Ω (⊙EM (S n)) ⊙≃ ⊙EM n
      spectrum 0 = spectrum0
      spectrum 1 = spectrum1
      spectrum (S (S n)) = spectrumSS n

module EMExplicit {i} (G : AbGroup i) where
  module HSpace = EM₁HSpace G
  open EMImplicit HSpace.H-⊙EM₁ public

  open BelowDiagonal public using (πS-below)

  πS-diag : (n : ℕ) → πS n (⊙EM (S n)) ≃ᴳ AbGroup.grp G
  πS-diag n = π₁-EM₁ (AbGroup.grp G) ∘eᴳ OnDiagonal.πS-diag n

  open AboveDiagonal public using (πS-above)
  open Spectrum public using (spectrum)
