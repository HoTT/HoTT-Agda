{-# OPTIONS --without-K #-}

open import HoTT
open import lib.Group
import lib.types.KG1
open import homotopy.HSpace renaming (HSpaceStructure to HSS)
open import homotopy.KG1HSpace
open import homotopy.LoopSpace
open import homotopy.Freudenthal
open import homotopy.IteratedSuspension
import homotopy.Pi2HSusp

module homotopy.KGn where

-- KGn when G is π₁(A)
module Implicit {i} (A : Type i) (cA : is-connected ⟨0⟩ A) 
  (gA : has-level ⟨ 1 ⟩ A) (A-H : HSS A) 
  (μcoh : HSS.μe- A-H (HSS.e A-H) == HSS.μ-e A-H (HSS.e A-H)) where

  a₀ = HSS.e A-H

  KG : ℕ → Type i
  KG O = (a₀ == a₀)
  KG (S n) = Trunc ⟨ S n ⟩ (Susp^ n A)
  
  kbase : (n : ℕ) → KG n
  kbase O = idp
  kbase (S n) = [ north^ n a₀ ]

  KG-conn : (n : ℕ) → is-connected ⟨ n ⟩ (KG (S n))
  KG-conn n = Trunc-preserves-conn ⟨ S n ⟩ 
                  (transport (λ t → is-connected t (Susp^ n A))
                    (nlemma n) (Susp^-conn n cA))
    where nlemma : (n : ℕ) → (n -2) +2+ ⟨0⟩ == ⟨ n ⟩
          nlemma O = idp
          nlemma (S n) = ap S (nlemma n)

  {-
  π (S k) (KG (S n)) (kbase (S n)) == π k (KG n) (kbase+ n)
  where k = S k' and n = S (S n')
  -}
  module Stable (k' n' : ℕ) (indexing : k' ≤ S n') where

    private
      {- need k,n ≥ 1 -}
      k : ℕ
      k = S k'

      n : ℕ
      n = S (S n')

      lte : ⟨ k ⟩ ≤T ⟨ n ⟩
      lte = ⟨⟩-monotone-≤ $ match indexing withl (λ p → inl (ap S p))
                                           withr (λ lt → inr (<-ap-S lt))

      kle : k ≤ (S n') *2
      kle = ≤-trans (≤-ap-S indexing) (lemma n') 
        where lemma : (n' : ℕ) → S (S n') ≤ (S n') *2
              lemma O = inl idp
              lemma (S n') = ≤-trans (≤-ap-S (lemma n')) (inr ltS)

    module SS = Susp^Stable A a₀ cA n' k' kle

    stable : π (S k) (KG (S n)) (kbase (S n)) == π k (KG n) (kbase n) 
    stable = 
      π (S k) (KG (S n)) (kbase (S n))
        =⟨ π-Trunc-≤T _ _ _ _ (≤T-ap-S lte) ⟩
      π (S k) (Susp^ n A) (north^ n a₀)
        =⟨ SS.stable ⟩
      π k (Susp^ (S n') A) (north^ (S n') a₀)
        =⟨ ! (π-Trunc-≤T _ _ _ _ lte) ⟩
      π k (KG n) (kbase n) ∎


  module BelowDiagonal where

    π₀ : (n : ℕ) → π 0 (KG (S n)) (kbase (S n)) == Lift Unit
    π₀ n = ua $ contr-equiv-LiftUnit $ connected-at-level-is-contr 
             (raise-level-≤T (≤T-ap-S (≤T-ap-S (-2≤T (n -2))))
                             (Trunc-level {n = ⟨0⟩}))
             (Trunc-preserves-conn ⟨0⟩ (KG-conn n))

    π₁ : (n : ℕ) → π 1 (KG (S (S n))) (kbase (S (S n))) == Lift Unit
    π₁ n = ua $ contr-equiv-LiftUnit $ connected-at-level-is-contr 
             (raise-level-≤T (≤T-ap-S (≤T-ap-S (-2≤T (n -2)))) 
                             (Trunc-level {n = ⟨0⟩}))
             (Trunc-preserves-conn ⟨0⟩ (path-conn (KG-conn (S n))))

    -- could probably avoid some of this clutter
    π-below : (k n : ℕ) → (k < n) → π k (KG n) (kbase n) == Lift Unit
    π-below 0 .1 ltS = π₀ 0
    π-below 0 (S n) (ltSR _) = π₀ n
    π-below 1 .2 ltS = π₁ 0
    π-below 1 .3 (ltSR ltS) = π₁ 1
    π-below 1 (S (S n)) (ltSR (ltSR _)) = π₁ n
    π-below (S (S k)) ._ ltS = 
      Stable.stable k k (inr ltS) ∙ π-below (S k) _ ltS
    π-below (S (S k)) ._ (ltSR ltS) = 
      Stable.stable k (S k) (inr (ltSR ltS)) ∙ π-below (S k) _ (ltSR ltS)
    π-below (S (S k)) ._ (ltSR (ltSR ltS)) = 
      Stable.stable k (S (S k)) (inr (ltSR (ltSR ltS))) 
      ∙ π-below (S k) _ (ltSR (ltSR ltS))
    π-below (S (S k)) (S (S (S n))) (ltSR (ltSR (ltSR lt))) =
      Stable.stable k n (inr (<-cancel-S (<-cancel-S (ltSR (ltSR (ltSR lt))))))
      ∙ π-below (S k) _ (<-cancel-S (ltSR (ltSR (ltSR lt))))

  module OnDiagonal where

    π₁ : π 1 (KG 1) (kbase 1) == π 1 A a₀
    π₁ = 
      Trunc ⟨0⟩ ([ a₀ ] == [ a₀ ]) 
        =⟨ ap (Trunc ⟨0⟩) $ ua (Trunc=-equiv [ a₀ ] [ a₀ ]) ⟩ 
      Trunc ⟨0⟩ (Trunc ⟨0⟩ (a₀ == a₀))
        =⟨ ua (fuse-Trunc (a₀ == a₀) ⟨0⟩ ⟨0⟩) ⟩
      Trunc ⟨0⟩ (a₀ == a₀) ∎

    module Π₂ = homotopy.Pi2HSusp A gA cA A-H μcoh

    π₂ : π 2 (KG 2) (kbase 2) == π 1 A a₀
    π₂ = 
      Trunc ⟨0⟩ (Ω^ 2 (Trunc ⟨ 2 ⟩ (Suspension A)) [ north A ])
        =⟨ ! (ap (Trunc ⟨0⟩) (Trunc-Ω^-path ⟨0⟩ 2 (Suspension A) (north A))) ⟩
      Trunc ⟨0⟩ (Trunc ⟨0⟩ (Ω^ 2 (Suspension A) (north A)))
        =⟨ ua (fuse-Trunc _ ⟨0⟩ ⟨0⟩) ⟩
      Trunc ⟨0⟩ (Ω^ 2 (Suspension A) (north A))
        =⟨ Π₂.π₂-Suspension ⟩
      Trunc ⟨0⟩ (Ω^ 1 A a₀) ∎

    π-diag : (n : ℕ) → π n (KG n) (kbase n) == π 1 A a₀
    π-diag 0 = idp
    π-diag 1 = π₁
    π-diag 2 = π₂
    π-diag (S (S (S n))) = Stable.stable (S n) n (inl idp) ∙ π-diag (S (S n))

  module AboveDiagonal where

    πS-0 : (k : ℕ) →  π (S k) (KG 0) (kbase 0) == Lift Unit
    πS-0 k = ua $ contr-equiv-LiftUnit $ inhab-prop-is-contr
      [ idp^ (S k) _ _ ]
      (Trunc-preserves-level ⟨0⟩ (Ω^-level-in ⟨-1⟩ (S k) _ _ 
        (raise-level-≤T (lemma k) (gA a₀ a₀))))
      where lemma : (k : ℕ) → ⟨ 0 ⟩ ≤T ((S k -2) +2+ ⟨-1⟩)
            lemma O = inl idp
            lemma (S k) = ≤T-trans (lemma k) (inr ltS)

    π-above : (k n : ℕ) →  (n < k) → π k (KG n) (kbase n) == Lift Unit
    π-above .1 O ltS = πS-0 0
    π-above (S n) O (ltSR lt) = πS-0 n
    π-above k (S n) lt = ua $ contr-equiv-LiftUnit $ inhab-prop-is-contr
      [ idp^ k _ _ ] 
      (Trunc-preserves-level ⟨0⟩ (Ω^-level-in ⟨-1⟩ k _ _ 
        (raise-level-≤T (lemma lt) Trunc-level)))
      where lemma : {k n : ℕ} → S n < k → ⟨ S n ⟩ ≤T ((k -2) +2+ ⟨-1⟩)
            lemma ltS = inl (+2+-comm ⟨-1⟩ _)
            lemma (ltSR lt) = ≤T-trans (lemma lt) (inr ltS) 

  module Spectrum where

    spectrum0 : (kbase 1 == kbase 1) == KG 0
    spectrum0 = ua $ unTrunc-equiv _ (gA a₀ a₀) ∘e Trunc=-equiv [ _ ] [ _ ]

    private
      module Π₂ = homotopy.Pi2HSusp A gA cA A-H μcoh

    spectrum1 : (kbase 2 == kbase 2) == KG 1
    spectrum1 = 
      Path {A = KG 2} [ north A ] [ north A ]
        =⟨ ua $ Trunc=-equiv [ north A ] [ north A ] ⟩ 
      Trunc ⟨ 1 ⟩ (north A == north A)
        =⟨ Π₂.main-lemma ⟩
      A
        =⟨ ! (ua $ unTrunc-equiv A gA) ⟩
      Trunc ⟨ 1 ⟩ A ∎

    private
      sconn : (n : ℕ) → is-connected (S (S (n -1))) (Susp^ (S n) A)
      sconn n = transport (λ t → is-connected t (Susp^ (S n) A))
                          (lemma n) (Susp^-conn (S n) cA)
        where lemma : (n : ℕ) → S ((n -2) +2+ ⟨0⟩) == S (S (n -1))
              lemma O = idp
              lemma (S n) = ap S (lemma n)

      kle : (n : ℕ) → ⟨ S (S n) ⟩ ≤T S ((n -1) +2+ S (n -1))
      kle O = inl idp
      kle (S n) = ≤T-trans (≤T-ap-S (kle n)) 
                   (≤T-trans (inl (! (+2+-βr (S n -1) (S n -1)))) 
                               (inr ltS))

      module FS (n : ℕ) = FreudenthalEquiv (n -1) (⟨ S (S n) ⟩) (kle n)
                            (Susp^ (S n) A) (north^ (S n) a₀) (sconn n)

    spectrumSS : (n : ℕ)
      → (kbase (S (S (S n))) == kbase (S (S (S n)))) == KG (S (S n))
    spectrumSS n = 
      Path {A = KG (S (S (S n)))} [ north _ ] [ north _ ]
        =⟨ ua $ Trunc=-equiv [ north _ ] [ north _ ] ⟩ 
      Trunc ⟨ S (S n) ⟩ (north (Susp^ (S n) A) == north (Susp^ (S n) A))
        =⟨ ! (FS.path n) ⟩
      KG (S (S n)) ∎

    spectrum : (n : ℕ) → Path {A = KG (S n)} (kbase _) (kbase _) == KG n
    spectrum 0 = spectrum0
    spectrum 1 = spectrum1
    spectrum (S (S n)) = spectrumSS n

module Explicit {i} {A : Type i} (G : AbelianGroup A) where
  module KG1 = lib.types.KG1 (fst G)
  module KGn = Implicit KG1.KG1 KG1.KG1-conn KG1.klevel (H-KG1 G) (μcoh G)

  open KGn public using (KG ; kbase)
  open KGn.BelowDiagonal public using (π-below)
  open KGn.OnDiagonal public using (π-diag)
  open KGn.AboveDiagonal public using (π-above)
  open KGn.Spectrum public using (spectrum)
