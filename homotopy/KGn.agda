{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.HSpace renaming (HSpaceStructure to HSS)
open import homotopy.Freudenthal
open import homotopy.IterSuspensionStable
open import homotopy.Pi2HSusp
open import homotopy.KG1HSpace

module homotopy.KGn where

-- K(G,n) when G is π₁(A,a₀)
module KGnImplicit {i} (A : Type i) (cA : is-connected ⟨0⟩ A)
  (gA : has-level ⟨ 1 ⟩ A) (A-H : HSS A)
  (μcoh : HSS.μe- A-H (HSS.e A-H) == HSS.μ-e A-H (HSS.e A-H)) where

  private
    a₀ = HSS.e A-H
    X = ∙[ A , a₀ ]

  Ptd-KG : (n : ℕ) → Ptd i
  Ptd-KG O = Ptd-Ω X
  Ptd-KG (S n) = Ptd-Trunc ⟨ S n ⟩ (Ptd-Susp^ n X)

  module _ (n : ℕ) where
    KG = fst (Ptd-KG n)
    kbase = snd (Ptd-KG n)

  KG-level : (n : ℕ) → has-level ⟨ n ⟩ (fst (Ptd-KG n))
  KG-level O = gA a₀ a₀
  KG-level (S n) = Trunc-level

  KG-conn : (n : ℕ) → is-connected ⟨ n ⟩ (KG (S n))
  KG-conn n = Trunc-preserves-conn ⟨ S n ⟩
                  (transport (λ t → is-connected t (fst (Ptd-Susp^ n X)))
                    (nlemma n) (Ptd-Susp^-conn n cA))
    where nlemma : (n : ℕ) → (n -2) +2+ ⟨0⟩ == ⟨ n ⟩
          nlemma O = idp
          nlemma (S n) = ap S (nlemma n)

  {-
  π (S k) (KG (S n)) (kbase (S n)) == π k (KG n) (kbase+ n)
  where k > 0 and n = S (S n')
  -}
  module Stable (k n' : ℕ) (tk : k ≠ 0) (tsk : S k ≠ 0)
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
      stable : π (S k) tsk (Ptd-KG (S n))
             == π k tk (Ptd-KG n)
      stable =
        π (S k) tsk (Ptd-KG (S n))
          =⟨ π-Trunc-≤T-iso _ tsk _ _ (≤T-ap-S lte) ⟩
        π (S k) tsk (Ptd-Susp^ n X)
          =⟨ SS.stable ⟩
        π k tk (Ptd-Susp^ (S n') X)
          =⟨ ! (π-Trunc-≤T-iso _ tk _ _ lte) ⟩
        π k tk (Ptd-KG n) ∎

  module BelowDiagonal where

    π₁ : (n : ℕ) (t1 : 1 ≠ 0 )
      → π 1 t1 (Ptd-KG (S (S n))) == LiftUnit-Group
    π₁ n t1 = transport
      (λ pi → pi 1 t1 (Ptd-KG (S (S n))) == LiftUnit-Group)
      π-fold
      (contr-iso-LiftUnit (π-concrete 1 t1 (Ptd-KG (S (S n))))
         (connected-at-level-is-contr
           (raise-level-≤T (≤T-ap-S (≤T-ap-S (-2≤T (n -2))))
                           (Trunc-level {n = ⟨0⟩}))
           (Trunc-preserves-conn ⟨0⟩ (path-conn (KG-conn (S n))))))

    -- some clutter here arises from the definition of <;
    -- any simple way to avoid this?
    π-below : (k n : ℕ) (tk : k ≠ 0) → (k < n)
      → π k tk (Ptd-KG n) == LiftUnit-Group
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
      → π 1 tn (Ptd-KG 1) == π 1 t1 X
    π₁ tn t1 =
      π-Trunc-≤T-iso 1 tn ⟨ 1 ⟩ X ≤T-refl
      ∙ ap (λ t → π 1 t X)
           (prop-has-all-paths (Π-level (λ _ → ⊥-is-prop)) tn t1)

    private
      module Π₂ = Pi2HSusp A gA cA A-H μcoh

    π₂ : (tn : 2 ≠ O) (t1 : 1 ≠ O)
      → π 2 tn (Ptd-KG 2) == π 1 t1 X
    π₂ tn t1 =
      π-Trunc-≤T-iso 2 tn ⟨ 2 ⟩ (Ptd-Susp X) ≤T-refl
      ∙ Π₂.π₂-Suspension t1 tn

    π-diag : (n : ℕ) (tn : n ≠ 0) (t1 : 1 ≠ O)
      → π n tn (Ptd-KG n) == π 1 t1 X
    π-diag 0 tn _ = ⊥-rec (tn idp)
    π-diag 1 tn t1 = π₁ tn t1
    π-diag 2 tn t1 = π₂ tn t1
    π-diag (S (S (S n))) tn t1 =
      Stable.stable (S (S n)) n (ℕ-S≠O _) tn ≤-refl
      ∙ π-diag (S (S n)) (ℕ-S≠O _) t1

  module AboveDiagonal where

    π-above : (k n : ℕ) (tk : k ≠ 0) → (n < k)
      → π k tk (Ptd-KG n) == LiftUnit-Group
    π-above k n tk lt = transport
      (λ pi → pi k tk (Ptd-KG n) == LiftUnit-Group)
      π-fold
      (contr-iso-LiftUnit (π-concrete k tk (Ptd-KG n))
        (inhab-prop-is-contr
          [ idp^ k ]
          (Trunc-preserves-level ⟨0⟩ (Ω^-level-in ⟨-1⟩ k _
            (raise-level-≤T (lemma lt) (KG-level n))))))
      where lemma : {k n : ℕ} → n < k → S (S (n -2)) ≤T ((k -2) +2+ ⟨-1⟩)
            lemma ltS = inl (! (+2+-comm _ ⟨-1⟩))
            lemma (ltSR lt) = ≤T-trans (lemma lt) (inr ltS)

  module Spectrum where

    private
      module Π₂ = Pi2HSusp A gA cA A-H μcoh

    spectrum0 : Ptd-Ω (Ptd-KG 1) == Ptd-KG 0
    spectrum0 =
      Ptd-Ω (Ptd-KG 1)
        =⟨ ptd-ua (Trunc=-equiv _ _) idp ⟩
      Ptd-Trunc ⟨ 0 ⟩ (Ptd-Ω X)
        =⟨ ptd-ua (unTrunc-equiv _ (gA a₀ a₀)) idp ⟩
      Ptd-Ω X ∎

    spectrum1 : Ptd-Ω (Ptd-KG 2) == Ptd-KG 1
    spectrum1 =
      Ptd-Ω (Ptd-KG 2)
        =⟨ ptd-ua (Trunc=-equiv _ _) idp ⟩
      Ptd-Trunc ⟨ 1 ⟩ (Ptd-Ω (Ptd-Susp X))
        =⟨ Π₂.ptd-main-lemma ⟩
      X
        =⟨ ! (ptd-ua (unTrunc-equiv _ gA) idp) ⟩
      Ptd-KG 1 ∎

    private
      nlemma : (n : ℕ) → Path {A = ℕ₋₂} (S ((n -2) +2+ ⟨0⟩)) (S (S (n -1)))
      nlemma O = idp
      nlemma (S n) = ap S (nlemma n)

      sconn : (n : ℕ) → is-connected (S (S (n -1))) (fst (Ptd-Susp^ (S n) X))
      sconn n = transport (λ t → is-connected t (fst (Ptd-Susp^ (S n) X)))
                          (nlemma n) (Ptd-Susp^-conn (S n) cA)

      kle : (n : ℕ) → ⟨ S (S n) ⟩ ≤T S ((n -1) +2+ S (n -1))
      kle O = inl idp
      kle (S n) = ≤T-trans (≤T-ap-S (kle n))
                   (≤T-trans (inl (! (+2+-βr (S n -1) (S n -1))))
                               (inr ltS))

      module FS (n : ℕ) =
        FreudenthalEquiv (n -1) (⟨ S (S n) ⟩) (kle n)
          (fst (Ptd-Susp^ (S n) X)) (snd (Ptd-Susp^ (S n) X)) (sconn n)

    spectrumSS : (n : ℕ)
      → Ptd-Ω (Ptd-KG (S (S (S n)))) == Ptd-KG (S (S n))
    spectrumSS n =
      Ptd-Ω (Ptd-KG (S (S (S n))))
        =⟨ ptd-ua (Trunc=-equiv _ _) idp ⟩
      Ptd-Trunc ⟨ S (S n) ⟩ (Ptd-Ω (Ptd-Susp^ (S (S n)) X))
        =⟨ ! (FS.ptd-path n) ⟩
      Ptd-KG (S (S n)) ∎

    abstract
      spectrum : (n : ℕ) → Ptd-Ω (Ptd-KG (S n)) == Ptd-KG n
      spectrum 0 = spectrum0
      spectrum 1 = spectrum1
      spectrum (S (S n)) = spectrumSS n

module KGnExplicit {i} (G : Group i) (G-abelian : is-abelian G) where
  module K1 = KG1 G
  module HSpace = KG1HSpace G G-abelian
  module Kn = KGnImplicit K1.KG1 K1.KG1-conn K1.klevel HSpace.H-KG1 HSpace.μcoh

  open Kn public

  open BelowDiagonal public using (π-below)

  π-diag : (n : ℕ) (tn : n ≠ 0) → π n tn (Ptd-KG n) == G
  π-diag n tn =
    OnDiagonal.π-diag n tn (ℕ-S≠O 0) ∙ K1.π₁.π₁-iso

  open AboveDiagonal public using (π-above)
  open Spectrum public -- using (spectrum)
