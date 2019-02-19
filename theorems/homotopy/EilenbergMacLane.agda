{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.HSpace renaming (HSpaceStructure to HSS)
open import homotopy.Freudenthal
open import homotopy.IterSuspensionStable
open import homotopy.Pi2HSusp
open import homotopy.EM1HSpace
open import homotopy.EilenbergMacLane1

module homotopy.EilenbergMacLane where

private
  -- helper
  kle : (n : ℕ) → ⟨ S (S n) ⟩ ≤T ⟨ n ⟩ +2+ ⟨ n ⟩
  kle O = inl idp
  kle (S n) = ≤T-trans (≤T-ap-S (kle n))
                (≤T-trans (inl (! (+2+-βr ⟨ n ⟩ ⟨ n ⟩)))
                            (inr ltS))

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
        ⊙≃⟨ ⊙Ω-⊙Trunc-comm 0 X ⟩
      ⊙Trunc 0 (⊙Ω X)
        ⊙≃⟨ ⊙unTrunc-equiv (⊙Ω X) ⟩
      ⊙Ω X ⊙≃∎

    spectrum1 : ⊙Ω (⊙EM 2) ⊙≃ ⊙EM 1
    spectrum1 =
      ⊙Ω (⊙EM 2)
        ⊙≃⟨ ⊙Ω-⊙Trunc-comm 1 (⊙Susp (de⊙ X)) ⟩
      ⊙Trunc 1 (⊙Ω (⊙Susp (de⊙ X)))
        ⊙≃⟨ Π₂.⊙eq ⟩
      ⊙EM 1 ⊙≃∎

    sconn : (n : ℕ) → is-connected ⟨ S n ⟩ (de⊙ (⊙Susp^ (S n) X))
    sconn n = ⊙Susp^-conn' (S n)

    module FS (n : ℕ) =
      FreudenthalEquiv ⟨ n ⟩₋₁ ⟨ S (S n) ⟩ (kle n)
        (⊙Susp^ (S n) X) {{sconn n}}

    Trunc-fmap-σloop-is-equiv : ∀ (n : ℕ)
      → is-equiv (Trunc-fmap {n = ⟨ S n ⟩} (σloop (⊙Susp^ n X)))
    Trunc-fmap-σloop-is-equiv O = snd (Π₂.eq ⁻¹)
    Trunc-fmap-σloop-is-equiv (S n) = snd (FS.eq n)

    spectrumSS : (n : ℕ)
      → ⊙Ω (⊙EM (S (S (S n)))) ⊙≃ ⊙EM (S (S n))
    spectrumSS n =
      ⊙Ω (⊙EM (S (S (S n))))
        ⊙≃⟨ ⊙Ω-⊙Trunc-comm ⟨ S (S n) ⟩ (⊙Susp^ (S (S n)) X) ⟩
      ⊙Trunc ⟨ S (S n) ⟩ (⊙Ω (⊙Susp^ (S (S n)) X))
        ⊙≃⟨ FS.⊙eq n ⊙⁻¹ ⟩
      ⊙EM (S (S n)) ⊙≃∎

    ⊙–>-spectrumSS : ∀ (n : ℕ)
      → ⊙–> (spectrumSS n) ◃⊙idf
        =⊙∘
        FS.⊙encodeN n ◃⊙∘
        ⊙–> (⊙Ω-⊙Trunc-comm ⟨ S (S n) ⟩ (⊙Susp^ (S (S n)) X)) ◃⊙idf
    ⊙–>-spectrumSS n =
      ⊙–> (spectrumSS n) ◃⊙idf
        =⊙∘⟨ =⊙∘-in {gs = ⊙<– (FS.⊙eq n) ◃⊙∘
                          ⊙–> (⊙Ω-⊙Trunc-comm ⟨ S (S n) ⟩ (⊙Susp^ (S (S n)) X)) ◃⊙idf} $
             ⊙λ= (⊙∘-unit-l _) ⟩
      ⊙<– (FS.⊙eq n) ◃⊙∘
      ⊙–> (⊙Ω-⊙Trunc-comm ⟨ S (S n) ⟩ (⊙Susp^ (S (S n)) X)) ◃⊙idf
        =⊙∘₁⟨ 0 & 1 & FS.⊙<–-⊙eq n ⟩
      FS.⊙encodeN n ◃⊙∘
      ⊙–> (⊙Ω-⊙Trunc-comm ⟨ S (S n) ⟩ (⊙Susp^ (S (S n)) X)) ◃⊙idf ∎⊙∘

    spectrum : (n : ℕ) → ⊙Ω (⊙EM (S n)) ⊙≃ ⊙EM n
    spectrum 0 = spectrum0
    spectrum 1 = spectrum1
    spectrum (S (S n)) = spectrumSS n

module EMImplicitMap {i} {j} {X : Ptd i} {Y : Ptd j} (f : X ⊙→ Y)
  {{_ : is-connected 0 (de⊙ X)}} {{_ : is-connected 0 (de⊙ Y)}}
  {{X-level : has-level 1 (de⊙ X)}} {{Y-level : has-level 1 (de⊙ Y)}}
  (H-X : HSS X) (H-Y : HSS Y) where

  ⊙EM-fmap : ∀ n → EMImplicit.⊙EM H-X n ⊙→ EMImplicit.⊙EM H-Y n
  ⊙EM-fmap O = ⊙Ω-fmap f
  ⊙EM-fmap (S n) = ⊙Trunc-fmap (⊙Susp^-fmap n f)

module SpectrumNatural {i} {X Y : Ptd i} (f : X ⊙→ Y)
  {{_ : is-connected 0 (de⊙ X)}} {{_ : is-connected 0 (de⊙ Y)}}
  {{X-level : has-level 1 (de⊙ X)}} {{Y-level : has-level 1 (de⊙ Y)}}
  (H-X : HSS X) (H-Y : HSS Y) where

  open EMImplicitMap f H-X H-Y

  open EMImplicit.Spectrum

  ⊙–>-spectrum0-natural :
    ⊙–> (spectrum0 H-Y) ◃⊙∘
    ⊙Ω-fmap (⊙Trunc-fmap f) ◃⊙idf
    =⊙∘
    ⊙Ω-fmap f ◃⊙∘
    ⊙–> (spectrum0 H-X) ◃⊙idf
  ⊙–>-spectrum0-natural =
    ⊙–> (spectrum0 H-Y) ◃⊙∘
    ⊙Ω-fmap (⊙Trunc-fmap f) ◃⊙idf
      =⊙∘⟨ 0 & 1 & ⊙expand (⊙–> (⊙unTrunc-equiv (⊙Ω Y)) ◃⊙∘
                            ⊙–> (⊙Ω-⊙Trunc-comm 0 Y) ◃⊙idf) ⟩
    ⊙–> (⊙unTrunc-equiv (⊙Ω Y)) ◃⊙∘
    ⊙–> (⊙Ω-⊙Trunc-comm 0 Y) ◃⊙∘
    ⊙Ω-fmap (⊙Trunc-fmap f) ◃⊙idf
      =⊙∘⟨ 1 & 2 & ⊙–>-⊙Ω-⊙Trunc-comm-natural-=⊙∘ 0 f ⟩
    ⊙–> (⊙unTrunc-equiv (⊙Ω Y)) ◃⊙∘
    ⊙Trunc-fmap (⊙Ω-fmap f) ◃⊙∘
    ⊙–> (⊙Ω-⊙Trunc-comm (S (S ⟨-2⟩)) X) ◃⊙idf
      =⊙∘⟨ 0 & 2 & ⊙–>-⊙unTrunc-equiv-natural-=⊙∘ (⊙Ω-fmap f) ⟩
    ⊙Ω-fmap f ◃⊙∘
    ⊙–> (⊙unTrunc-equiv (⊙Ω X)) ◃⊙∘
    ⊙–> (⊙Ω-⊙Trunc-comm (S (S ⟨-2⟩)) X) ◃⊙idf
      =⊙∘⟨ 1 & 2 & ⊙contract ⟩
    ⊙Ω-fmap f ◃⊙∘
    ⊙–> (spectrum0 H-X) ◃⊙idf ∎⊙∘

  ⊙–>-spectrum1-natural :
    ⊙–> (spectrum1 H-Y) ◃⊙∘
    ⊙Ω-fmap (⊙Trunc-fmap (⊙Susp-fmap (fst f))) ◃⊙idf
    =⊙∘
    ⊙Trunc-fmap f ◃⊙∘
    ⊙–> (spectrum1 H-X) ◃⊙idf
  ⊙–>-spectrum1-natural =
    ⊙–> (spectrum1 H-Y) ◃⊙∘
    ⊙Ω-fmap (⊙Trunc-fmap (⊙Susp-fmap (fst f))) ◃⊙idf
      =⊙∘⟨ 0 & 1 & ⊙expand (⊙–> (Pi2HSusp.⊙eq H-Y) ◃⊙∘
                            ⊙–> (⊙Ω-⊙Trunc-comm 1 (⊙Susp (de⊙ Y))) ◃⊙idf) ⟩
    ⊙–> (Pi2HSusp.⊙eq H-Y) ◃⊙∘
    ⊙–> (⊙Ω-⊙Trunc-comm 1 (⊙Susp (de⊙ Y))) ◃⊙∘
    ⊙Ω-fmap (⊙Trunc-fmap (⊙Susp-fmap (fst f))) ◃⊙idf
      =⊙∘⟨ 1 & 2 & ⊙–>-⊙Ω-⊙Trunc-comm-natural-=⊙∘ 1 (⊙Susp-fmap (fst f)) ⟩
    ⊙–> (Pi2HSusp.⊙eq H-Y) ◃⊙∘
    ⊙Trunc-fmap (⊙Ω-fmap (⊙Susp-fmap (fst f))) ◃⊙∘
    ⊙–> (⊙Ω-⊙Trunc-comm 1 (⊙Susp (de⊙ X))) ◃⊙idf
      =⊙∘⟨ 0 & 2 & Pi2HSuspNaturality.⊙encodeN-natural f H-X H-Y ⟩
    ⊙Trunc-fmap f ◃⊙∘
    ⊙–> (Pi2HSusp.⊙eq H-X) ◃⊙∘
    ⊙–> (⊙Ω-⊙Trunc-comm (S (S (S ⟨-2⟩))) (⊙Susp (de⊙ X))) ◃⊙idf
      =⊙∘⟨ 1 & 2 & ⊙contract ⟩
    ⊙Trunc-fmap f ◃⊙∘
    ⊙–> (spectrum1 H-X) ◃⊙idf ∎⊙∘

  ⊙–>-spectrumSS-natural : ∀ (n : ℕ)
    → ⊙–> (spectrumSS H-Y n) ◃⊙∘
      ⊙Ω-fmap (⊙Trunc-fmap (⊙Susp^-fmap (S (S n)) f)) ◃⊙idf
      =⊙∘
      ⊙Trunc-fmap (⊙Susp^-fmap (S n) f) ◃⊙∘
      ⊙–> (spectrumSS H-X n) ◃⊙idf
  ⊙–>-spectrumSS-natural n =
    ⊙–> (spectrumSS H-Y n) ◃⊙∘
    ⊙Ω-fmap (⊙Trunc-fmap (⊙Susp^-fmap (S (S n)) f)) ◃⊙idf
      =⊙∘⟨ 0 & 1 & ⊙–>-spectrumSS H-Y n ⟩
    FS.⊙encodeN H-Y n ◃⊙∘
    ⊙–> (⊙Ω-⊙Trunc-comm ⟨ S (S n) ⟩ (⊙Susp^ (S (S n)) Y)) ◃⊙∘
    ⊙Ω-fmap (⊙Trunc-fmap (⊙Susp^-fmap (S (S n)) f)) ◃⊙idf
      =⊙∘⟨ 1 & 2 & ⊙–>-⊙Ω-⊙Trunc-comm-natural-=⊙∘ ⟨ S (S n) ⟩ (⊙Susp^-fmap (S (S n)) f) ⟩
    FS.⊙encodeN H-Y n ◃⊙∘
    ⊙Trunc-fmap (⊙Ω-fmap (⊙Susp^-fmap (S (S n)) f)) ◃⊙∘
    ⊙–> (⊙Ω-⊙Trunc-comm ⟨ S (S n) ⟩ (⊙Susp^ (S (S n)) X)) ◃⊙idf
      =⊙∘⟨ 0 & 2 & FreudenthalEquivNatural.⊙encodeN-natural
             ⟨ n ⟩₋₁ ⟨ S (S n) ⟩ (kle n)
             {X = ⊙Susp^ (S n) X} {Y = ⊙Susp^ (S n) Y} (⊙Susp^-fmap (S n) f)
             {{sconn H-X n}} {{sconn H-Y n}} ⟩
    ⊙Trunc-fmap (⊙Susp^-fmap (S n) f) ◃⊙∘
    FS.⊙encodeN H-X n ◃⊙∘
    ⊙–> (⊙Ω-⊙Trunc-comm ⟨ S (S n) ⟩ (⊙Susp^ (S (S n)) X)) ◃⊙idf
      =⊙∘⟨ 1 & 2 & !⊙∘ $ ⊙–>-spectrumSS H-X n ⟩
    ⊙Trunc-fmap (⊙Susp^-fmap (S n) f) ◃⊙∘
    ⊙–> (spectrumSS H-X n) ◃⊙idf ∎⊙∘

  abstract
    ⊙–>-spectrum-natural : ∀ (n : ℕ)
      → ⊙–> (spectrum H-Y n) ◃⊙∘
        ⊙Ω-fmap (⊙EM-fmap (S n)) ◃⊙idf
        =⊙∘
        ⊙EM-fmap n ◃⊙∘
        ⊙–> (spectrum H-X n) ◃⊙idf
    ⊙–>-spectrum-natural 0 = ⊙–>-spectrum0-natural
    ⊙–>-spectrum-natural 1 = ⊙–>-spectrum1-natural
    ⊙–>-spectrum-natural (S (S n)) = ⊙–>-spectrumSS-natural n

    ⊙<–-spectrum-natural : ∀ (n : ℕ)
      → ⊙<– (spectrum H-Y n) ◃⊙∘
        ⊙EM-fmap n ◃⊙idf
        =⊙∘
        ⊙Ω-fmap (⊙EM-fmap (S n)) ◃⊙∘
        ⊙<– (spectrum H-X n) ◃⊙idf
    ⊙<–-spectrum-natural n =
      ⊙<– (spectrum H-Y n) ◃⊙∘
      ⊙EM-fmap n ◃⊙idf
        =⊙∘⟨ 2 & 0 & !⊙∘ $ ⊙<–-inv-r-=⊙∘ (spectrum H-X n) ⟩
      ⊙<– (spectrum H-Y n) ◃⊙∘
      ⊙EM-fmap n ◃⊙∘
      ⊙–> (spectrum H-X n) ◃⊙∘
      ⊙<– (spectrum H-X n) ◃⊙idf
        =⊙∘⟨ 1 & 2 & !⊙∘ (⊙–>-spectrum-natural n) ⟩
      ⊙<– (spectrum H-Y n) ◃⊙∘
      ⊙–> (spectrum H-Y n) ◃⊙∘
      ⊙Ω-fmap (⊙Trunc-fmap (⊙Susp^-fmap n f)) ◃⊙∘
      ⊙<– (spectrum H-X n) ◃⊙idf
        =⊙∘⟨ 0 & 2 & ⊙<–-inv-l-=⊙∘ (spectrum H-Y n) ⟩
      ⊙Ω-fmap (⊙Trunc-fmap (⊙Susp^-fmap n f)) ◃⊙∘
      ⊙<– (spectrum H-X n) ◃⊙idf ∎⊙∘

module EMExplicit {i} (G : AbGroup i) where
  module HSpace = EM₁HSpace G
  open EMImplicit
    {X = ⊙EM₁ (AbGroup.grp G)}
    {{EM₁-conn}}
    {{EM₁-level₁ (AbGroup.grp G)}}
    HSpace.H-⊙EM₁ public

  open BelowDiagonal public using (πS-below)

  πS-diag : (n : ℕ) → πS n (⊙EM (S n)) ≃ᴳ AbGroup.grp G
  πS-diag n = π₁-EM₁ (AbGroup.grp G) ∘eᴳ OnDiagonal.πS-diag n

  open AboveDiagonal public using (πS-above)

  abstract
    spectrum : (n : ℕ) → ⊙Ω (⊙EM (S n)) ⊙≃ ⊙EM n
    spectrum = Spectrum.spectrum

    spectrum-def : ∀ n → spectrum n == Spectrum.spectrum n
    spectrum-def n = idp
