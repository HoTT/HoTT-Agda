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

  KG1+ : ℕ → Type i
  KG1+ n = Trunc ⟨ S n ⟩ (Susp^ n A)

  KG1+-conn : (n : ℕ) → is-connected ⟨ n ⟩ (KG1+ n)
  KG1+-conn n = Trunc-preserves-conn ⟨ S n ⟩ 
                  (transport (λ t → is-connected t (Susp^ n A))
                    (nlemma n) (Susp^-conn n cA))
    where nlemma : (n : ℕ) → (n -2) +2+ ⟨0⟩ == ⟨ n ⟩
          nlemma O = idp
          nlemma (S n) = ap S (nlemma n)

  kbase : ∀ n → KG1+ n
  kbase n = [ north^ n a₀ ]

  {-
  π (S k) (KG1+ (S n)) (kbase (S n)) == π k (KG1+ n) (kbase n) 
  where k = S k' and n = S n'
  -}
  module Stable (k' n' : ℕ) (indexing : k' ≤ S n') where

    private
      {- need k,n ≥ 1 -}
      k : ℕ
      k = S k'

      n : ℕ
      n = S n'

      lte : ⟨ k ⟩ ≤T ⟨ S n ⟩
      lte = ⟨⟩-monotone-≤ $ match indexing withl (λ p → inl (ap S p))
                                           withr (λ lt → inr (<-ap-S lt))

      kle : k ≤ n *2
      kle = ≤-trans (≤-ap-S indexing) (lemma n') 
        where lemma : (n' : ℕ) → S (S n') ≤ (S n') *2
              lemma O = inl idp
              lemma (S n') = ≤-trans (≤-ap-S (lemma n')) (inr ltS)

    module SS = Susp^Stable A a₀ cA n' k' kle

    stable : π (S k) (KG1+ (S n)) (kbase (S n)) == π k (KG1+ n) (kbase n) 
    stable = 
      π (S k) (KG1+ (S n)) (kbase (S n)) 
        =⟨ π-Trunc-≤T _ _ _ _ (≤T-ap-S lte) ⟩
      π (S k) (Susp^ (S n) A) (north^ (S n) a₀)
        =⟨ SS.stable ⟩
      π k (Susp^ n A) (north^ n a₀)
        =⟨ ! (π-Trunc-≤T _ _ _ _ lte) ⟩
      π k (KG1+ n) (kbase n) ∎

  module Zero where

    π₀ : (n : ℕ) → π 0 (KG1+ n) (kbase n) == Lift Unit
    π₀ n = ua (contr-equiv-LiftUnit (connected-at-level-is-contr 
              (raise-level-≤T (≤T-ap-S (≤T-ap-S (-2≤T (n -2))))
                              (Trunc-level {n = ⟨0⟩}))
              (Trunc-preserves-conn ⟨0⟩ (KG1+-conn n))))

  module BelowDiagonal where

    π₁ : (n : ℕ) → π 1 (KG1+ (S n)) (kbase (S n)) == Lift Unit
    π₁ n = ua (contr-equiv-LiftUnit (connected-at-level-is-contr 
              (raise-level-≤T (≤T-ap-S (≤T-ap-S (-2≤T (n -2)))) 
                              (Trunc-level {n = ⟨0⟩}))
              (Trunc-preserves-conn ⟨0⟩ (path-conn (KG1+-conn (S n))))))

    -- could probably avoid some of this clutter
    π-below : (k n : ℕ) → (k < S n) → π k (KG1+ n) (kbase n) == Lift Unit
    π-below O n lt = Zero.π₀ n
    π-below 1 .1 ltS = π₁ 0
    π-below 1 .2 (ltSR ltS) = π₁ 1
    π-below 1 (S n) (ltSR (ltSR _)) = π₁ n
    π-below (S (S k)) .(S (S k)) ltS = 
      Stable.stable k k (inr ltS) ∙ π-below (S k) (S k) ltS
    π-below (S (S k)) .(S (S (S k))) (ltSR ltS) = 
      Stable.stable k (S k) (inr (ltSR ltS)) ∙ π-below (S k) (S (S k)) (ltSR ltS)
    π-below (S (S k)) .(S (S (S (S k)))) (ltSR (ltSR ltS)) = 
      Stable.stable k (S (S k)) (inr (ltSR (ltSR ltS))) 
      ∙ π-below (S k) (S (S (S k))) (ltSR (ltSR ltS))
    π-below (S (S k)) (S (S n)) (ltSR (ltSR (ltSR lt))) =
      Stable.stable k n (inr (<-cancel-S (<-cancel-S (ltSR (ltSR (ltSR lt))))))
       ∙ π-below (S k) (S n) (<-cancel-S (ltSR (ltSR (ltSR lt))))


  module OnDiagonal where

    π₁ : π 1 (KG1+ 0) (kbase 0) == π 1 A a₀
    π₁ = 
      Trunc ⟨0⟩ ([ a₀ ] == [ a₀ ]) 
        =⟨ ap (Trunc ⟨0⟩) $ ua (Trunc=-equiv [ a₀ ] [ a₀ ]) ⟩ 
      Trunc ⟨0⟩ (Trunc ⟨0⟩ (a₀ == a₀))
        =⟨ ua (fuse-Trunc (a₀ == a₀) ⟨0⟩ ⟨0⟩) ⟩
      Trunc ⟨0⟩ (a₀ == a₀) ∎

    module Π₂ = homotopy.Pi2HSusp A gA cA A-H μcoh

    π₂ : π 2 (KG1+ 1) (kbase 1) == π 1 A a₀
    π₂ = 
      Trunc ⟨0⟩ (Ω^ 2 (Trunc ⟨ 2 ⟩ (Suspension A)) [ north A ])
        =⟨ ! (ap (Trunc ⟨0⟩) (Trunc-Ω^-path ⟨0⟩ 2 (Suspension A) (north A))) ⟩
      Trunc ⟨0⟩ (Trunc ⟨0⟩ (Ω^ 2 (Suspension A) (north A)))
        =⟨ ua (fuse-Trunc _ ⟨0⟩ ⟨0⟩) ⟩
      Trunc ⟨0⟩ (Ω^ 2 (Suspension A) (north A))
        =⟨ Π₂.π₂-Suspension ⟩
      Trunc ⟨0⟩ (Ω^ 1 A a₀) ∎

    π-diag : (n : ℕ) → π (S n) (KG1+ n) (kbase n) == π 1 A a₀
    π-diag 0 = π₁
    π-diag 1 = π₂
    π-diag (S (S n)) = Stable.stable (S n) n (inl idp) ∙ π-diag (S n)

  module AboveDiagonal where

    π-above : (k n : ℕ) →  S n < k → π k (KG1+ n) (kbase n) == Lift Unit
    π-above k n lt = ua $ contr-equiv-LiftUnit $ inhab-prop-is-contr
      [ idp^ k _ _ ] 
      (Trunc-preserves-level ⟨0⟩ (Ω^-level-in ⟨-1⟩ k _ _ 
        (raise-level-≤T (lemma lt) Trunc-level)))
      where lemma : {k n : ℕ} → S n < k → ⟨ S n ⟩ ≤T ((k -2) +2+ ⟨-1⟩)
            lemma ltS = inl (+2+-comm ⟨-1⟩ _)
            lemma (ltSR lt) = ≤T-trans (lemma lt) (inr ltS) 

module Explicit {i} (G : AbelianGroup i) where
  module KG1 = lib.types.KG1 (fst G)
  module KGn = Implicit KG1.KG1 KG1.KG1-conn KG1.klevel (H-KG1 G) (μcoh G)

  open KGn public using (KG1+ ; kbase)

  π-below : (k n : ℕ) → (k < S n) → π k (KG1+ n) (kbase n) == Lift Unit
  π-below = KGn.BelowDiagonal.π-below

  π-diag : (n : ℕ) → π (S n) (KG1+ n) (kbase n) == Group.El (fst G)
  π-diag n = KGn.OnDiagonal.π-diag n ∙ KG1.π₁.π₁-path

  π-above : (k n : ℕ) → (S n < k) → π k (KG1+ n) (kbase n) == Lift Unit
  π-above = KGn.AboveDiagonal.π-above


