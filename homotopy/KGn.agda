{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.HSpace renaming (HSpaceStructure to HSS)
open import homotopy.Freudenthal
open import homotopy.IteratedSuspension
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

  Ptd-KG : (n : ℕ) ⦃ _ : n ≠ O ⦄ → Ptd i
  Ptd-KG O ⦃ posi ⦄ = ⊥-rec (posi idp)
  Ptd-KG (S n) ⦃ _ ⦄ = Ptd-Trunc ⟨ S n ⟩ (Ptd-Susp^ n X)

  KG : (n : ℕ) ⦃ _ : n ≠ O ⦄ → Type i
  KG n = fst (Ptd-KG n)
  
  kbase : (n : ℕ) ⦃ _ : n ≠ O ⦄ → KG n
  kbase n = snd (Ptd-KG n)

  KG-level : (n : ℕ) ⦃ _ : n ≠ O ⦄ → has-level ⟨ n ⟩ (fst (Ptd-KG n))
  KG-level O ⦃ posi ⦄ = ⊥-rec (posi idp)
  KG-level (S n) ⦃ _ ⦄ = Trunc-level

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
  module Stable (k n' : ℕ) ⦃ pk : k ≠ 0 ⦄ ⦃ psk : S k ≠ 0 ⦄
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
      module SS = Susp^Stable X cA (S n') k ⦃ pk ⦄ ⦃ psk ⦄ kle

    abstract
      stable : π (S k) ⦃ psk ⦄ (Ptd-KG (S n))
             == π k ⦃ pk ⦄ (Ptd-KG n)
      stable = 
        π (S k) ⦃ psk ⦄ (Ptd-KG (S n))
          =⟨ π-Trunc-≤T-iso _ ⦃ psk ⦄ _ _ (≤T-ap-S lte) ⟩
        π (S k) ⦃ psk ⦄ (Ptd-Susp^ n X) 
          =⟨ SS.stable ⟩ 
        π k ⦃ pk ⦄ (Ptd-Susp^ (S n') X)
          =⟨ ! (π-Trunc-≤T-iso _ ⦃ pk ⦄ _ _ lte) ⟩
        π k ⦃ pk ⦄ (Ptd-KG n) ∎

  module BelowDiagonal where

    π₁ : (n : ℕ) → ⦃ p1 : 1 ≠ 0 ⦄ 
      → π 1 ⦃ p1 ⦄ (Ptd-KG (S (S n))) == LiftUnit-Group
    π₁ n ⦃ p1 ⦄ = transport 
      (λ pi → pi 1 ⦃ p1 ⦄ (Ptd-KG (S (S n))) == LiftUnit-Group) 
      π-fold 
      (contr-iso-LiftUnit (π-concrete 1 ⦃ p1 ⦄ (Ptd-KG (S (S n)))) 
         (connected-at-level-is-contr 
           (raise-level-≤T (≤T-ap-S (≤T-ap-S (-2≤T (n -2))))
                           (Trunc-level {n = ⟨0⟩})) 
           (Trunc-preserves-conn ⟨0⟩ (path-conn (KG-conn (S n))))))

    -- some clutter here arises from the definition of <; 
    -- any simple way to avoid this?
    π-below : (k n : ℕ) → ⦃ pk : k ≠ 0 ⦄ → ⦃ pn : n ≠ 0 ⦄ → (k < n) 
      → π k ⦃ pk ⦄ (Ptd-KG n ⦃ pn ⦄) == LiftUnit-Group
    π-below 0 _ ⦃ pk ⦄ lt = ⊥-rec (pk idp)
    π-below 1 .2 ⦃ pk ⦄ ltS = π₁ 0 ⦃ pk ⦄
    π-below 1 .3 ⦃ pk ⦄ (ltSR ltS) = π₁ 1 ⦃ pk ⦄
    π-below 1 (S (S n)) ⦃ pk ⦄ (ltSR (ltSR _)) = π₁ n ⦃ pk ⦄
    π-below (S (S k)) ._ ⦃ pssk ⦄ ltS = 
      Stable.stable (S k) k ⦃ ℕ-S≠O k ⦄ ⦃ pssk ⦄ (inr ltS) 
      ∙ π-below (S k) _ ⦃ ℕ-S≠O k ⦄ ⦃ pssk ⦄ ltS
    π-below (S (S k)) ._ ⦃ pssk ⦄ (ltSR ltS) = 
      Stable.stable (S k) (S k) ⦃ ℕ-S≠O k ⦄ ⦃ pssk ⦄ (inr (ltSR ltS)) 
      ∙ π-below (S k) _ ⦃ ℕ-S≠O k ⦄ ⦃ ℕ-S≠O (S (S k)) ⦄ (ltSR ltS) 
    π-below (S (S k)) ._ ⦃ pssk ⦄ (ltSR (ltSR ltS)) = 
      Stable.stable (S k) (S (S k)) ⦃ ℕ-S≠O k ⦄ ⦃ pssk ⦄ (inr (ltSR (ltSR ltS)))
      ∙ π-below (S k) _ ⦃ ℕ-S≠O k ⦄ ⦃ ℕ-S≠O (S (S (S k))) ⦄ (ltSR (ltSR ltS))
    π-below (S (S k)) (S (S (S n))) ⦃ pssk ⦄ (ltSR (ltSR (ltSR lt))) = 
      Stable.stable (S k) n ⦃ ℕ-S≠O k ⦄ ⦃ pssk ⦄ (inr (<-cancel-S (ltSR (ltSR (ltSR lt))))) 
      ∙ π-below (S k) _ ⦃ ℕ-S≠O k ⦄ ⦃ ℕ-S≠O (S n) ⦄ (<-cancel-S (ltSR (ltSR (ltSR lt))))


  module OnDiagonal where

    π₁ : ⦃ pn : 1 ≠ O ⦄ → ⦃ p1 : 1 ≠ O ⦄ 
      → π 1 ⦃ pn ⦄ (Ptd-KG 1 ⦃ ℕ-S≠O 0 ⦄) == π 1 ⦃ p1 ⦄ X
    π₁ ⦃ pn ⦄ ⦃ p1 ⦄ = 
      π-Trunc-≤T-iso 1 ⦃ pn ⦄ ⟨ 1 ⟩ X ≤T-refl 
      ∙ ap (λ p → π 1 ⦃ p ⦄ X) 
           (prop-has-all-paths (Π-level (λ _ → ⊥-is-prop)) pn p1)

    private
      module Π₂ = Pi2HSusp A gA cA A-H μcoh

    π₂ : ⦃ pn : 2 ≠ O ⦄ → ⦃ p1 : 1 ≠ O ⦄ 
      → π 2 ⦃ pn ⦄ (Ptd-KG 2 ⦃ ℕ-S≠O 1 ⦄) == π 1 ⦃ p1 ⦄ X
    π₂ ⦃ pn ⦄ ⦃ p1 ⦄ = 
      π-Trunc-≤T-iso 2 ⦃ pn ⦄ ⟨ 2 ⟩ (Ptd-Susp X) ≤T-refl 
      ∙ Π₂.π₂-Suspension ⦃ p1 ⦄ ⦃ pn ⦄

    π-diag : (n : ℕ) → ⦃ pn : n ≠ 0 ⦄ → ⦃ p1 : 1 ≠ O ⦄
      → π n ⦃ pn ⦄ (Ptd-KG n) == π 1 ⦃ p1 ⦄ X
    π-diag 0 ⦃ pn ⦄ ⦃ _ ⦄ = ⊥-rec (pn idp)
    π-diag 1 ⦃ pn ⦄ ⦃ p1 ⦄ = π₁ ⦃ pn ⦄ ⦃ p1 ⦄
    π-diag 2 ⦃ pn ⦄ ⦃ p1 ⦄ = π₂ ⦃ pn ⦄ ⦃ p1 ⦄
    π-diag (S (S (S n))) ⦃ pn ⦄ ⦃ p1 ⦄ = 
      Stable.stable (S (S n)) n ⦃ psk = pn ⦄ ≤-refl 
      ∙ π-diag (S (S n)) ⦃ p1 = p1 ⦄ 

  module AboveDiagonal where

    π-above : (k n : ℕ) → ⦃ pk : k ≠ 0 ⦄ → ⦃ pn : n ≠ 0 ⦄ → (n < k)
      → π k (Ptd-KG n) == LiftUnit-Group
    π-above k n lt = transport
      (λ pi → pi k (Ptd-KG n) == LiftUnit-Group)
      π-fold
      (contr-iso-LiftUnit (π-concrete k (Ptd-KG n)) 
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

    spectrum₁ : Ptd-Ω (Ptd-KG 2) == Ptd-KG 1
    spectrum₁ = 
      Ptd-Ω (Ptd-KG 2)
        =⟨ ptd-ua (Trunc=-equiv _ _) idp ⟩
      Ptd-Trunc ⟨ 1 ⟩ (Ptd-Ω (Ptd-Susp X))
        =⟨ Π₂.ptd-main-lemma ⟩
      X
        =⟨ ! (ptd-ua (unTrunc-equiv A gA) idp) ⟩
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
      spectrum : (n : ℕ) ⦃ pn : n ≠ 0 ⦄ → Ptd-Ω (Ptd-KG (S n)) == Ptd-KG n
      spectrum 0 ⦃ pn ⦄ = ⊥-rec (pn idp)
      spectrum 1 ⦃ _ ⦄ = spectrum₁
      spectrum (S (S n)) ⦃ _ ⦄ = spectrumSS n
  
module KGnExplicit {i} (G : Group i) (G-abelian : is-abelian G) where
  module K1 = KG1 G 
  module HSpace = KG1HSpace G G-abelian
  module Kn = KGnImplicit K1.KG1 K1.KG1-conn K1.klevel HSpace.H-KG1 HSpace.μcoh

  open Kn public 
  open Kn.BelowDiagonal public using (π-below)

  π-diag : (n : ℕ) → ⦃ pn : n ≠ 0 ⦄ → ⦃ p1 : 1 ≠ O ⦄
    → π n ⦃ pn ⦄ (Ptd-KG n) == G --π 1 ⦃ p1 ⦄ X
  π-diag n ⦃ pn ⦄ ⦃ p1 ⦄ = 
    Kn.OnDiagonal.π-diag n ⦃ pn ⦄ ⦃ p1 ⦄ ∙ K1.π₁.π₁-iso ⦃ p1 ⦄

  open Kn.AboveDiagonal public using (π-above)
  open Kn.Spectrum public using (spectrum)
