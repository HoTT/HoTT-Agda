{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane
open import homotopy.SmashFmapConn
open import homotopy.IterSuspSmash
open import homotopy.EilenbergMacLaneFunctor
open import cohomology.CupProduct.OnEM.InLowDegrees
open import cohomology.CupProduct.OnEM.InLowDegrees2
open import cohomology.CupProduct.OnEM.InAllDegrees
open import cohomology.CupProduct.OnEM.CommutativityInLowDegrees using (⊙∧-cp₀₀-comm)
open import cohomology.CupProduct.OnEM.CommutativityInLowDegrees2

module cohomology.CupProduct.OnEM.CommutativityInAllDegrees {i} {j} (G : AbGroup i) (H : AbGroup j) where

open EMExplicit

private
  module G = AbGroup G
  module H = AbGroup H
  module G⊗H = TensorProduct G H
  module H⊗G = TensorProduct H G

⊙∧-cpₕₕ'-comm : ∀ (m n : ℕ) -- (x : ⊙Susp^ m (⊙EM₁ G.grp) ∧ ⊙Susp^ n (⊙EM₁ H.grp))
  → ⊙transport (⊙EM H⊗G.abgroup) (+-comm (S m) (S n)) ◃⊙∘
    ⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S m + S n) ◃⊙∘
    ⊙∧-cpₕₕ' G H m n ◃⊙idf
    =⊙∘
    ⊙cond-neg H⊗G.abgroup (S n + S m) (and (odd (S m)) (odd (S n))) ◃⊙∘
    ⊙∧-cpₕₕ' H G n m ◃⊙∘
    ⊙∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) ◃⊙idf
⊙∧-cpₕₕ'-comm m n =
  ⊙transport (⊙EM H⊗G.abgroup) (+-comm (S m) (S n)) ◃⊙∘
  ⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S m + S n) ◃⊙∘
  ⊙∧-cpₕₕ' G H m n ◃⊙idf
    =⊙∘₁⟨ 1 & 1 & ! $ ⊙transport-⊙EM-uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative (S m + S n) ⟩
  ⊙transport (⊙EM H⊗G.abgroup) (+-comm (S m) (S n)) ◃⊙∘
  ⊙transport (λ K → ⊙EM K (S (m + S n))) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative) ◃⊙∘
  ⊙∧-cpₕₕ' G H m n ◃⊙idf
    =⊙∘⟨ 2 & 1 & ⊙expand (⊙∧-cpₕₕ'-seq G H m n) ⟩
  ⊙transport (⊙EM H⊗G.abgroup) (+-comm (S m) (S n)) ◃⊙∘
  ⊙transport (λ K → ⊙EM K (S (m + S n))) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative) ◃⊙∘
  ⊙cpₕₕ'' G⊗H.abgroup m n ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙∧-cp₁₁ G H) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n ◃⊙idf
    =⊙∘⟨ 1 & 2 & !⊙∘ $ ⊙transport-natural-=⊙∘
           (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative)
           (λ K → ⊙cpₕₕ'' K m n) ⟩
  ⊙transport (⊙EM H⊗G.abgroup) (+-comm (S m) (S n)) ◃⊙∘
  ⊙cpₕₕ'' H⊗G.abgroup m n ◃⊙∘
  ⊙transport (λ K → ⊙Susp^ (m + n) (⊙EM K 2)) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙∧-cp₁₁ G H) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n ◃⊙idf
    =⊙∘₁⟨ 2 & 1 & p₁ ⟩
  ⊙transport (⊙EM H⊗G.abgroup) (+-comm (S m) (S n)) ◃⊙∘
  ⊙cpₕₕ'' H⊗G.abgroup m n ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙Trunc-fmap (⊙Susp^-fmap 1 (⊙EM₁-fmap G⊗H.swap))) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙∧-cp₁₁ G H) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n ◃⊙idf
    =⊙∘⟨ 1 & 1 & ⊙expand (⊙cpₕₕ''-seq H⊗G.abgroup m n) ⟩
  ⊙transport (⊙EM H⊗G.abgroup) (+-comm (S m) (S n)) ◃⊙∘
  ⊙cond-neg H⊗G.abgroup (S m + S n) (odd n) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S m) n)) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (m + n) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙Trunc-fmap (⊙Susp^-fmap 1 (⊙EM₁-fmap G⊗H.swap))) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙∧-cp₁₁ G H) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n ◃⊙idf
    =⊙∘⟨ 0 & 2 & !⊙∘ $ ⊙transport-natural-=⊙∘
           (+-comm (S m) (S n))
           (λ k → ⊙cond-neg H⊗G.abgroup k (odd n)) ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (odd n) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (+-comm (S m) (S n)) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S m) n)) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (m + n) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙Trunc-fmap (⊙Susp^-fmap 1 (⊙EM₁-fmap G⊗H.swap))) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙∧-cp₁₁ G H) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n ◃⊙idf
    =⊙∘⟨ 1 & 2 & !⊙∘ $ ⊙transport-∙ (⊙EM H⊗G.abgroup) (! (+-βr (S m) n)) (+-comm (S m) (S n)) ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (odd n) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S m) n) ∙ +-comm (S m) (S n)) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (m + n) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙Trunc-fmap (⊙Susp^-fmap 1 (⊙EM₁-fmap G⊗H.swap))) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙∧-cp₁₁ G H) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n ◃⊙idf
    =⊙∘₁⟨ 1 & 1 & ap (⊙transport (⊙EM H⊗G.abgroup)) $
          set-path ℕ-level (! (+-βr (S m) n) ∙ +-comm (S m) (S n))
                           (ap (λ k → S (S k)) (+-comm m n) ∙ ! (+-βr (S n) m)) ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (odd n) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (ap (λ k → S (S k)) (+-comm m n) ∙ ! (+-βr (S n) m)) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (m + n) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙Trunc-fmap (⊙Susp^-fmap 1 (⊙EM₁-fmap G⊗H.swap))) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙∧-cp₁₁ G H) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n ◃⊙idf
    =⊙∘⟨ 1 & 1 & ⊙transport-∙ (⊙EM H⊗G.abgroup)
           (ap (λ k → S (S k)) (+-comm m n))
           (! (+-βr (S n) m)) ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (odd n) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S n) m)) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (ap (λ k → S (S k)) (+-comm m n)) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (m + n) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙Trunc-fmap (⊙Susp^-fmap 1 (⊙EM₁-fmap G⊗H.swap))) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙∧-cp₁₁ G H) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n ◃⊙idf
    =⊙∘₁⟨ 2 & 1 & ⊙transport-⊙coe (⊙EM H⊗G.abgroup) (ap (λ k → S (S k)) (+-comm m n)) ∙
                  ap ⊙coe (∘-ap (⊙EM H⊗G.abgroup) (λ k → S (S k)) (+-comm m n)) ∙
                  ! (⊙transport-⊙coe (λ k → ⊙EM H⊗G.abgroup (S (S k))) (+-comm m n)) ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (odd n) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S n) m)) ◃⊙∘
  ⊙transport (λ k → ⊙EM H⊗G.abgroup (S (S k))) (+-comm m n) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (m + n) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙Trunc-fmap (⊙Susp^-fmap 1 (⊙EM₁-fmap G⊗H.swap))) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙∧-cp₁₁ G H) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n ◃⊙idf
    =⊙∘⟨ 4 & 2 & ⊙Susp^-fmap-seq-=⊙∘ (m + n) (⊙∧-cp₁₁-comm G H) ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (odd n) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S n) m)) ◃⊙∘
  ⊙transport (λ k → ⊙EM H⊗G.abgroup (S (S k))) (+-comm m n) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (m + n) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙EM-neg H⊗G.abgroup 2) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙∧-cp₁₁ H G) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n ◃⊙idf
    =⊙∘⟨ 2 & 2 & !⊙∘ $ ⊙transport-natural-=⊙∘ (+-comm m n) (⊙EM2-Susp H⊗G.abgroup) ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (odd n) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S n) m)) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (n + m) ◃⊙∘
  ⊙transport (λ k → ⊙Susp^ k (⊙EM H⊗G.abgroup 2)) (+-comm m n) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙EM-neg H⊗G.abgroup 2) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙∧-cp₁₁ H G) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n ◃⊙idf
    =⊙∘⟨ 3 & 2 & !⊙∘ $ ⊙transport-natural-=⊙∘
           (+-comm m n)
           (λ k → ⊙Susp^-fmap k (⊙EM-neg H⊗G.abgroup 2)) ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (odd n) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S n) m)) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (n + m) ◃⊙∘
  ⊙Susp^-fmap (n + m) (⊙EM-neg H⊗G.abgroup 2) ◃⊙∘
  ⊙transport (λ k → ⊙Susp^ k (⊙EM H⊗G.abgroup 2)) (+-comm m n) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙∧-cp₁₁ H G) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n ◃⊙idf
    =⊙∘⟨ 4 & 2 & !⊙∘ $ ⊙transport-natural-=⊙∘
           (+-comm m n)
           (λ k → ⊙Susp^-fmap k (⊙∧-cp₁₁ H G)) ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (odd n) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S n) m)) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (n + m) ◃⊙∘
  ⊙Susp^-fmap (n + m) (⊙EM-neg H⊗G.abgroup 2) ◃⊙∘
  ⊙Susp^-fmap (n + m) (⊙∧-cp₁₁ H G) ◃⊙∘
  ⊙transport (λ k → ⊙Susp^ k (⊙EM₁ H.grp ⊙∧ ⊙EM₁ G.grp)) (+-comm m n) ◃⊙∘
  ⊙Susp^-fmap (m + n) (⊙∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n ◃⊙idf
    =⊙∘⟨ 5 & 3 & ⊙Σ^∧Σ^-out-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (odd n) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S n) m)) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (n + m) ◃⊙∘
  ⊙Susp^-fmap (n + m) (⊙EM-neg H⊗G.abgroup 2) ◃⊙∘
  ⊙Susp^-fmap (n + m) (⊙∧-cp₁₁ H G) ◃⊙∘
  ⊙maybe-Susp^-flip (n + m) (and (odd n) (odd m)) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m ◃⊙∘
  ⊙∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) ◃⊙idf
    =⊙∘⟨ 4 & 2 & ⊙maybe-Susp^-flip-natural-=⊙∘ (⊙∧-cp₁₁ H G) (n + m) (and (odd n) (odd m)) ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (odd n) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S n) m)) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (n + m) ◃⊙∘
  ⊙Susp^-fmap (n + m) (⊙EM-neg H⊗G.abgroup 2) ◃⊙∘
  ⊙maybe-Susp^-flip (n + m) (and (odd n) (odd m)) ◃⊙∘
  ⊙Susp^-fmap (n + m) (⊙∧-cp₁₁ H G) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m ◃⊙∘
  ⊙∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) ◃⊙idf
    =⊙∘₁⟨ 3 & 1 & ! p₂ ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (odd n) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S n) m)) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (n + m) ◃⊙∘
  ⊙transport (λ K → ⊙Susp^ (n + m) (⊙EM K 2)) (inv-path H⊗G.abgroup) ◃⊙∘
  ⊙maybe-Susp^-flip (n + m) (and (odd n) (odd m)) ◃⊙∘
  ⊙Susp^-fmap (n + m) (⊙∧-cp₁₁ H G) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m ◃⊙∘
  ⊙∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) ◃⊙idf
    =⊙∘⟨ 2 & 2 & ⊙transport-natural-=⊙∘ (inv-path H⊗G.abgroup) (λ K → ⊙EM2-Susp K (n + m)) ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (odd n) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S n) m)) ◃⊙∘
  ⊙transport (λ K → ⊙EM K (S (S (n + m)))) (inv-path H⊗G.abgroup) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (n + m) ◃⊙∘
  ⊙maybe-Susp^-flip (n + m) (and (odd n) (odd m)) ◃⊙∘
  ⊙Susp^-fmap (n + m) (⊙∧-cp₁₁ H G) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m ◃⊙∘
  ⊙∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) ◃⊙idf
    =⊙∘⟨ 1 & 2 & ⊙transport-natural-=⊙∘
           (inv-path H⊗G.abgroup)
           (λ K → ⊙transport (⊙EM K) (! (+-βr (S n) m))) ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (odd n) ◃⊙∘
  ⊙transport (λ K → ⊙EM K (S n + S m)) (inv-path H⊗G.abgroup) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S n) m)) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (n + m) ◃⊙∘
  ⊙maybe-Susp^-flip (n + m) (and (odd n) (odd m)) ◃⊙∘
  ⊙Susp^-fmap (n + m) (⊙∧-cp₁₁ H G) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m ◃⊙∘
  ⊙∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) ◃⊙idf
    =⊙∘⟨ 3 & 2 & ⊙EM2-Susp-⊙maybe-Susp^-flip H⊗G.abgroup (n + m) (and (odd n) (odd m)) h₁ ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (odd n) ◃⊙∘
  ⊙transport (λ K → ⊙EM K (S n + S m)) (inv-path H⊗G.abgroup) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S n) m)) ◃⊙∘
  ⊙Trunc-fmap (⊙maybe-Susp-flip (⊙Susp^ (n + m) (⊙EM₁ H⊗G.grp)) (and (odd n) (odd m))) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (n + m) ◃⊙∘
  ⊙Susp^-fmap (n + m) (⊙∧-cp₁₁ H G) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m ◃⊙∘
  ⊙∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) ◃⊙idf
    =⊙∘₁⟨ 3 & 1 & ⊙maybe-Susp^-flip-⊙cond-neg
            H⊗G.abgroup (S n + m) (and (odd n) (odd m)) h₂ ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (odd n) ◃⊙∘
  ⊙transport (λ K → ⊙EM K (S n + S m)) (inv-path H⊗G.abgroup) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S n) m)) ◃⊙∘
  ⊙cond-neg H⊗G.abgroup (S (S (n + m))) (and (odd n) (odd m)) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (n + m) ◃⊙∘
  ⊙Susp^-fmap (n + m) (⊙∧-cp₁₁ H G) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m ◃⊙∘
  ⊙∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) ◃⊙idf
    =⊙∘⟨ 2 & 2 & !⊙∘ $ ⊙transport-natural-=⊙∘
           (! (+-βr (S n) m))
           (λ k → ⊙cond-neg H⊗G.abgroup k (and (odd n) (odd m))) ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (odd n) ◃⊙∘
  ⊙transport (λ K → ⊙EM K (S n + S m)) (inv-path H⊗G.abgroup) ◃⊙∘
  ⊙cond-neg H⊗G.abgroup (S n + S m) (and (odd n) (odd m)) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S n) m)) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (n + m) ◃⊙∘
  ⊙Susp^-fmap (n + m) (⊙∧-cp₁₁ H G) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m ◃⊙∘
  ⊙∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) ◃⊙idf
    =⊙∘⟨ 1 & 2 & ⊙cond-neg-∘ H⊗G.abgroup (S n + S m) true (and (odd n) (odd m)) ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (odd n) ◃⊙∘
  ⊙cond-neg H⊗G.abgroup (S (n + S m)) (negate (and (odd n) (odd m))) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S n) m)) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (n + m) ◃⊙∘
  ⊙Susp^-fmap (n + m) (⊙∧-cp₁₁ H G) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m ◃⊙∘
  ⊙∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) ◃⊙idf
    =⊙∘⟨ 0 & 2 & ⊙cond-neg-∘ H⊗G.abgroup (S n + S m) (odd n) (negate (and (odd n) (odd m))) ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (xor (odd n) (negate (and (odd n) (odd m)))) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S n) m)) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (n + m) ◃⊙∘
  ⊙Susp^-fmap (n + m) (⊙∧-cp₁₁ H G) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m ◃⊙∘
  ⊙∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) ◃⊙idf
    =⊙∘₁⟨ 0 & 1 & ap (⊙cond-neg H⊗G.abgroup (S n + S m)) (bp (odd n) (odd m)) ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (xor (and (negate (odd m)) (negate (odd n))) (odd m)) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S n) m)) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (n + m) ◃⊙∘
  ⊙Susp^-fmap (n + m) (⊙∧-cp₁₁ H G) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m ◃⊙∘
  ⊙∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) ◃⊙idf
    =⊙∘⟨ 0 & 1 & !⊙∘ $ ⊙cond-neg-∘ H⊗G.abgroup (S n + S m) (and (odd (S m)) (odd (S n))) (odd m) ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (and (odd (S m)) (odd (S n))) ◃⊙∘
  ⊙cond-neg H⊗G.abgroup (S n + S m) (odd m) ◃⊙∘
  ⊙transport (⊙EM H⊗G.abgroup) (! (+-βr (S n) m)) ◃⊙∘
  ⊙EM2-Susp H⊗G.abgroup (n + m) ◃⊙∘
  ⊙Susp^-fmap (n + m) (⊙∧-cp₁₁ H G) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m ◃⊙∘
  ⊙∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) ◃⊙idf
    =⊙∘⟨ 1 & 3 & ⊙contract ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (and (odd (S m)) (odd (S n))) ◃⊙∘
  ⊙cpₕₕ'' H⊗G.abgroup n m ◃⊙∘
  ⊙Susp^-fmap (n + m) (⊙∧-cp₁₁ H G) ◃⊙∘
  ⊙Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m ◃⊙∘
  ⊙∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) ◃⊙idf
    =⊙∘⟨ 1 & 3 & ⊙contract ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (and (odd (S m)) (odd (S n))) ◃⊙∘
  ⊙∧-cpₕₕ' H G n m ◃⊙∘
  ⊙∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) ◃⊙idf ∎⊙∘
  where
    p₁ : ⊙transport (λ K → ⊙Susp^ (m + n) (⊙EM K 2)) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative)
         == ⊙Susp^-fmap (m + n) (⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap 2)
    p₁ =
      ⊙transport (λ K → ⊙Susp^ (m + n) (⊙EM K 2)) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative)
        =⟨ ⊙transport-⊙coe
             (λ K → ⊙Susp^ (m + n) (⊙EM K 2))
             (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative) ⟩
      ⊙coe (ap (λ K → ⊙Susp^ (m + n) (⊙EM K 2)) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative))
        =⟨ ap ⊙coe (ap-∘ (⊙Susp^ (m + n)) (λ K → ⊙EM K 2) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative)) ⟩
      ⊙coe (ap (⊙Susp^ (m + n)) (ap (λ K → ⊙EM K 2) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative)))
        =⟨ ! $ ⊙transport-⊙coe
             (⊙Susp^ (m + n))
             (ap (λ K → ⊙EM K 2) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative)) ⟩
      ⊙transport (⊙Susp^ (m + n)) (ap (λ K → ⊙EM K 2) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative))
        =⟨ ⊙transport-⊙Susp^ (m + n) (ap (λ K → ⊙EM K 2) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative)) ⟩
      ⊙Susp^-fmap (m + n) (⊙coe (ap (λ K → ⊙EM K 2) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative)))
        =⟨ ap (⊙Susp^-fmap (m + n)) $ ! $
           ⊙transport-⊙coe (λ K → ⊙EM K 2) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative) ⟩
      ⊙Susp^-fmap (m + n) (⊙transport (λ K → ⊙EM K 2) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative))
        =⟨ ap (⊙Susp^-fmap (m + n)) (⊙transport-⊙EM-uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative 2) ⟩
      ⊙Susp^-fmap (m + n) (⊙Trunc-fmap (⊙Susp^-fmap 1 (⊙EM₁-fmap (–>ᴳ G⊗H.commutative)))) =∎
    p₂ : ⊙transport (λ K → ⊙Susp^ (n + m) (⊙EM K 2)) (inv-path H⊗G.abgroup)
         == ⊙Susp^-fmap (n + m) (⊙EM-neg H⊗G.abgroup 2)
    p₂ =
      ⊙transport (λ K → ⊙Susp^ (n + m) (⊙EM K 2)) (inv-path H⊗G.abgroup)
        =⟨ ⊙transport-⊙coe (λ K → ⊙Susp^ (n + m) (⊙EM K 2)) (inv-path H⊗G.abgroup) ⟩
      ⊙coe (ap (λ K → ⊙Susp^ (n + m) (⊙EM K 2)) (inv-path H⊗G.abgroup))
        =⟨ ap ⊙coe (ap-∘ (⊙Susp^ (n + m)) (λ K → ⊙EM K 2) (inv-path H⊗G.abgroup)) ⟩
      ⊙coe (ap (⊙Susp^ (n + m)) (ap (λ K → ⊙EM K 2) (inv-path H⊗G.abgroup)))
        =⟨ ! $ ⊙transport-⊙coe (⊙Susp^ (n + m)) (ap (λ K → ⊙EM K 2) (inv-path H⊗G.abgroup)) ⟩
      ⊙transport (⊙Susp^ (n + m)) (ap (λ K → ⊙EM K 2) (inv-path H⊗G.abgroup))
        =⟨ ⊙transport-⊙Susp^ (n + m) (ap (λ K → ⊙EM K 2) (inv-path H⊗G.abgroup)) ⟩
      ⊙Susp^-fmap (n + m) (⊙coe (ap (λ K → ⊙EM K 2) (inv-path H⊗G.abgroup)))
        =⟨ ap (⊙Susp^-fmap (n + m)) $ ! $
           ⊙transport-⊙coe (λ K → ⊙EM K 2) (inv-path H⊗G.abgroup) ⟩
      ⊙Susp^-fmap (n + m) (⊙transport (λ K → ⊙EM K 2) (inv-path H⊗G.abgroup))
        =⟨ ap (⊙Susp^-fmap (n + m)) $
           ⊙transport-⊙EM-uaᴬᴳ H⊗G.abgroup H⊗G.abgroup (inv-iso H⊗G.abgroup) 2 ⟩
      ⊙Susp^-fmap (n + m) (⊙EM-neg H⊗G.abgroup 2) =∎
    h₁ : n + m == 0 → and (odd n) (odd m) == false
    h₁ p = ap (λ k → and (odd k) (odd m)) (fst (+-0 n m p))
    h₂ : S (n + m) == 0 → and (odd n) (odd m) == inr unit
    h₂ p = ⊥-elim (ℕ-S≠O (n + m) p)
    bp : ∀ (b c : Bool) → xor b (negate (and b c)) == xor (and (negate c) (negate b)) c
    bp true  true  = idp
    bp true  false = idp
    bp false true  = idp
    bp false false = idp

⊙∧-cpₕₕ-comm : ∀ (m n : ℕ)
  → ⊙transport (⊙EM H⊗G.abgroup) (+-comm (S m) (S n)) ◃⊙∘
    ⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S m + S n) ◃⊙∘
    ⊙∧-cpₕₕ G H m n ◃⊙idf
    =⊙∘
    ⊙cond-neg H⊗G.abgroup (S n + S m) (and (odd (S m)) (odd (S n))) ◃⊙∘
    ⊙∧-cpₕₕ H G n m ◃⊙∘
    ⊙∧-swap (⊙EM G (S m)) (⊙EM H (S n)) ◃⊙idf
⊙∧-cpₕₕ-comm m n =
  =⊙∘-in $
  –>-is-inj ⊙Ext.⊙restr-equiv _ _ $
  =⊙∘-out
    {fs = ⊙transport (⊙EM H⊗G.abgroup) (+-comm (S m) (S n)) ◃⊙∘
          ⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S m + S n) ◃⊙∘
          ⊙∧-cpₕₕ G H m n ◃⊙∘
          ⊙smash-truncate G H m n ◃⊙idf}
    {gs = ⊙cond-neg H⊗G.abgroup (S n + S m) (and (odd (S m)) (odd (S n))) ◃⊙∘
          ⊙∧-cpₕₕ H G n m ◃⊙∘
          ⊙∧-swap (⊙EM G (S m)) (⊙EM H (S n)) ◃⊙∘
          ⊙smash-truncate G H m n ◃⊙idf} $
  ⊙transport (⊙EM H⊗G.abgroup) (+-comm (S m) (S n)) ◃⊙∘
  ⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S m + S n) ◃⊙∘
  ⊙∧-cpₕₕ G H m n ◃⊙∘
  ⊙smash-truncate G H m n ◃⊙idf
    =⊙∘₁⟨ 2 & 2 & SmashCPₕₕ.⊙ext-β G H m n (⊙∧-cpₕₕ' G H m n) ⟩
  ⊙transport (⊙EM H⊗G.abgroup) (+-comm (S m) (S n)) ◃⊙∘
  ⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S m + S n) ◃⊙∘
  ⊙∧-cpₕₕ' G H m n ◃⊙idf
    =⊙∘⟨ ⊙∧-cpₕₕ'-comm m n ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (and (odd (S m)) (odd (S n))) ◃⊙∘
  ⊙∧-cpₕₕ' H G n m ◃⊙∘
  ⊙∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) ◃⊙idf
    =⊙∘⟨ 1 & 1 & =⊙∘-in {gs = ⊙∧-cpₕₕ H G n m ◃⊙∘
                              ⊙smash-truncate H G n m ◃⊙idf} $
         ! $ SmashCPₕₕ.⊙ext-β H G n m (⊙∧-cpₕₕ' H G n m) ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (and (odd (S m)) (odd (S n))) ◃⊙∘
  ⊙∧-cpₕₕ H G n m ◃⊙∘
  ⊙smash-truncate H G n m ◃⊙∘
  ⊙∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) ◃⊙idf
    =⊙∘⟨ 2 & 2 & =⊙∘-in {gs = ⊙∧-swap (⊙EM G (S m)) (⊙EM H (S n)) ◃⊙∘
                              ⊙smash-truncate G H m n ◃⊙idf} $
         ⊙∧-swap-naturality
           ([_] {n = ⟨ S m ⟩} {A = Susp^ m (EM₁ G.grp)} , idp)
           ([_] {n = ⟨ S n ⟩} {A = Susp^ n (EM₁ H.grp)} , idp) ⟩
  ⊙cond-neg H⊗G.abgroup (S n + S m) (and (odd (S m)) (odd (S n))) ◃⊙∘
  ⊙∧-cpₕₕ H G n m ◃⊙∘
  ⊙∧-swap (⊙EM G (S m)) (⊙EM H (S n)) ◃⊙∘
  ⊙smash-truncate G H m n ◃⊙idf ∎⊙∘
  where
  module ⊙Ext = ⊙ConnExtend
    {Z = ⊙EM H⊗G.abgroup (S n + S m)}
    {n = ⟨ S n + S m ⟩}
    (⊙smash-truncate G H m n)
    (transport (λ l → has-conn-fibers l (smash-truncate G H m n))
               (ap ⟨_⟩ (+-comm (S m) (S n)))
               (smash-truncate-conn G H m n))
    (EM-level H⊗G.abgroup (S n + S m))

⊙∧-cp-comm : ∀ (m n : ℕ)
  → ⊙transport (⊙EM H⊗G.abgroup) (+-comm m n) ◃⊙∘
    ⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (m + n) ◃⊙∘
    ⊙∧-cp G H m n ◃⊙idf
    =⊙∘
    ⊙cond-neg H⊗G.abgroup (n + m) (and (odd m) (odd n)) ◃⊙∘
    ⊙∧-cp H G n m ◃⊙∘
    ⊙∧-swap (⊙EM G m) (⊙EM H n) ◃⊙idf
⊙∧-cp-comm O O =
  ⊙transport (⊙EM H⊗G.abgroup) (+-comm 0 0) ◃⊙∘
  ⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap 0 ◃⊙∘
  ⊙∧-cp G H 0 0 ◃⊙idf
    =⊙∘⟨ 0 & 1 & =⊙∘-in {gs = ⊙idf-seq} $
         ap (⊙transport (⊙EM H⊗G.abgroup)) (set-path ℕ-level (+-comm 0 0) idp) ⟩
  ⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap 0 ◃⊙∘
  ⊙∧-cp G H 0 0 ◃⊙idf
    =⊙∘⟨ ⊙∧-cp₀₀-comm G H ⟩
  ⊙∧-cp H G 0 0 ◃⊙∘
  ⊙∧-swap (⊙EM G 0) (⊙EM H 0) ◃⊙idf
    =⊙∘⟨ 0 & 0 & ⊙contract ⟩
  ⊙cond-neg H⊗G.abgroup 0 false ◃⊙∘
  ⊙∧-cp H G 0 0 ◃⊙∘
  ⊙∧-swap (⊙EM G 0) (⊙EM H 0) ◃⊙idf ∎⊙∘
⊙∧-cp-comm O (S n) =
  ⊙transport (⊙EM H⊗G.abgroup) (+-comm O (S n)) ◃⊙∘
  ⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S n) ◃⊙∘
  ⊙∧-cp₀ₕ G H n ◃⊙idf
    =⊙∘⟨ 3 & 0 & !⊙∘ $ ⊙∧-swap-inv (⊙EM G 0) (⊙EM H (S n)) ⟩
  ⊙transport (⊙EM H⊗G.abgroup) (+-comm O (S n)) ◃⊙∘
  ⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S n) ◃⊙∘
  ⊙∧-cp₀ₕ G H n ◃⊙∘
  ⊙∧-swap (⊙EM H (S n)) (⊙EM G 0) ◃⊙∘
  ⊙∧-swap (⊙EM G 0) (⊙EM H (S n)) ◃⊙idf
    =⊙∘⟨ 0 & 4 & ⊙contract ⟩
  ⊙∧-cpₕ₀ H G n ◃⊙∘
  ⊙∧-swap (⊙EM G 0) (⊙EM H (S n)) ◃⊙idf
    =⊙∘⟨ 0 & 0 & ⊙contract ⟩
  ⊙cond-neg H⊗G.abgroup (S n + O) false ◃⊙∘
  ⊙∧-cpₕ₀ H G n ◃⊙∘
  ⊙∧-swap (⊙EM G 0) (⊙EM H (S n)) ◃⊙idf ∎⊙∘
⊙∧-cp-comm (S m) O =
  ⊙transport (⊙EM H⊗G.abgroup) (+-comm (S m) O) ◃⊙∘
  ⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S m + 0) ◃⊙∘
  ⊙∧-cpₕ₀ G H m ◃⊙idf
    =⊙∘⟨ 0 & 2 & !⊙∘ $
         ⊙transport-natural-=⊙∘
           (+-comm (S m) 0)
           (⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap) ⟩
  ⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S m) ◃⊙∘
  ⊙transport (⊙EM G⊗H.abgroup) (+-comm (S m) O) ◃⊙∘
  ⊙∧-cpₕ₀ G H m ◃⊙idf
    =⊙∘⟨ 2 & 1 & ⊙expand (⊙∧-cpₕ₀-seq G H m) ⟩
  ⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S m) ◃⊙∘
  ⊙transport (⊙EM G⊗H.abgroup) (+-comm (S m) O) ◃⊙∘
  ⊙transport (⊙EM G⊗H.abgroup) (+-comm 0 (S m)) ◃⊙∘
  ⊙EM-fmap H⊗G.abgroup G⊗H.abgroup H⊗G.swap (S m) ◃⊙∘
  ⊙∧-cp₀ₕ H G m ◃⊙∘
  ⊙∧-swap (⊙EM G (S m)) (⊙EM H 0) ◃⊙idf
    =⊙∘⟨ 1 & 2 & !⊙∘ $ ⊙transport-∙
           (⊙EM G⊗H.abgroup) (+-comm 0 (S m)) (+-comm (S m) O) ⟩
  ⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S m) ◃⊙∘
  ⊙transport (⊙EM G⊗H.abgroup) (+-comm 0 (S m) ∙ +-comm (S m) O) ◃⊙∘
  ⊙EM-fmap H⊗G.abgroup G⊗H.abgroup H⊗G.swap (S m) ◃⊙∘
  ⊙∧-cp₀ₕ H G m ◃⊙∘
  ⊙∧-swap (⊙EM G (S m)) (⊙EM H 0) ◃⊙idf
    =⊙∘⟨ 1 & 1 & =⊙∘-in {gs = ⊙idf-seq} $
         ap (⊙transport (⊙EM G⊗H.abgroup)) $
         set-path ℕ-level (+-comm 0 (S m) ∙ +-comm (S m) O) idp ⟩
  ⊙EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S m) ◃⊙∘
  ⊙EM-fmap H⊗G.abgroup G⊗H.abgroup H⊗G.swap (S m) ◃⊙∘
  ⊙∧-cp₀ₕ H G m ◃⊙∘
  ⊙∧-swap (⊙EM G (S m)) (⊙EM H 0) ◃⊙idf
    =⊙∘₁⟨ 0 & 2 & ! $
          ⊙EM-fmap-∘ H⊗G.abgroup G⊗H.abgroup H⊗G.abgroup G⊗H.swap H⊗G.swap (S m) ⟩
  ⊙EM-fmap H⊗G.abgroup H⊗G.abgroup (G⊗H.swap ∘ᴳ H⊗G.swap) (S m) ◃⊙∘
  ⊙∧-cp₀ₕ H G m ◃⊙∘
  ⊙∧-swap (⊙EM G (S m)) (⊙EM H 0) ◃⊙idf
    =⊙∘₁⟨ 0 & 1 & ap (λ φ → ⊙EM-fmap H⊗G.abgroup H⊗G.abgroup φ (S m))
                     H⊗G.swap-swap-idhom ⟩
  ⊙EM-fmap H⊗G.abgroup H⊗G.abgroup (idhom H⊗G.grp) (S m) ◃⊙∘
  ⊙∧-cp₀ₕ H G m ◃⊙∘
  ⊙∧-swap (⊙EM G (S m)) (⊙EM H 0) ◃⊙idf
    =⊙∘⟨ 0 & 1 & =⊙∘-in {gs = ⊙idf-seq} $ ⊙EM-fmap-idhom H⊗G.abgroup (S m) ⟩
  ⊙∧-cp₀ₕ H G m ◃⊙∘
  ⊙∧-swap (⊙EM G (S m)) (⊙EM H 0) ◃⊙idf
    =⊙∘₁⟨ 0 & 0 & ap (⊙cond-neg H⊗G.abgroup (S m)) (! (and-false-r (odd (S m)))) ⟩
  ⊙cond-neg H⊗G.abgroup (S m) (and (odd (S m)) (odd O)) ◃⊙∘
  ⊙∧-cp₀ₕ H G m ◃⊙∘
  ⊙∧-swap (⊙EM G (S m)) (⊙EM H 0) ◃⊙idf ∎⊙∘
⊙∧-cp-comm (S m) (S n) = ⊙∧-cpₕₕ-comm m n
