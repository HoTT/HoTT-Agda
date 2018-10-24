{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane
open import homotopy.SmashFmapConn
open import homotopy.IterSuspSmash
open import homotopy.EilenbergMacLaneFunctor
open import cohomology.CupProduct.OnEM.InLowDegrees
open import cohomology.CupProduct.OnEM.InLowDegrees2
open import cohomology.CupProduct.OnEM.InAllDegrees
open import cohomology.CupProduct.OnEM.CommutativityInLowDegrees2

module cohomology.CupProduct.OnEM.CommutativityInAllDegrees {i} {j} (G : AbGroup i) (H : AbGroup j) where

open EMExplicit

private
  module G = AbGroup G
  module H = AbGroup H
  module G⊗H = TensorProduct G H
  module H⊗G = TensorProduct H G

cp-swap : ∀ (m n : ℕ)
  → EM G⊗H.abgroup (m + n) → EM H⊗G.abgroup (n + m)
cp-swap m n =
  transport (EM H⊗G.abgroup) (+-comm m n) ∘
  EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (m + n)

cpₕₕ'-comm : ∀ (m n : ℕ) (x : ⊙Susp^ m (⊙EM₁ G.grp) ∧ ⊙Susp^ n (⊙EM₁ H.grp))
  → (cp-swap (S m) (S n) $
     cpₕₕ' G H m n x)
    ==
    (cond-neg H⊗G.abgroup (S n + S m) (and (odd (S m)) (odd (S n))) $
     cpₕₕ' H G n m $
     ∧-swap _ _ x)
cpₕₕ'-comm m n x =
  (transport (EM H⊗G.abgroup) (+-comm (S m) (S n)) $
   EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap (S m + S n) $
   cpₕₕ' G H m n x)
    =⟨ ap (transport (EM H⊗G.abgroup) (+-comm (S m) (S n))) $
       app= (! (transport-EM-uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative (S m + S n))) $
       cpₕₕ' G H m n x ⟩
  (transport (EM H⊗G.abgroup) (+-comm (S m) (S n)) $
   transport (λ K → EM K (S m + S n)) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative) $
   cpₕₕ' G H m n x)
    =⟨ ap (transport (EM H⊗G.abgroup) (+-comm (S m) (S n))) $
       app= (! (transp-naturality {B = λ K → Susp^ (m + n) (EM K 2)}
                                  {C = λ K → EM K (S m + S n)}
                                  (λ {K} → cpₕₕ'' K m n)
                                  (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative))) $
       Susp^-fmap (m + n) (∧-cp₁₁ G H) $
       Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x ⟩
  (transport (EM H⊗G.abgroup) (+-comm (S m) (S n)) $
   cpₕₕ'' H⊗G.abgroup m n $
   transport (λ K → Susp^ (m + n) (EM K 2)) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative) $
   Susp^-fmap (m + n) (∧-cp₁₁ G H) $
   Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x)
    =⟨ ap (transport (EM H⊗G.abgroup) (+-comm (S m) (S n))) $
       ap (cpₕₕ'' H⊗G.abgroup m n) $
       app= p₁ $
       Susp^-fmap (m + n) (∧-cp₁₁ G H) $
       Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x ⟩
  (transport (EM H⊗G.abgroup) (+-comm (S m) (S n)) $
   cpₕₕ'' H⊗G.abgroup m n $
   Susp^-fmap (m + n) (EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap 2) $
   Susp^-fmap (m + n) (∧-cp₁₁ G H) $
   Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x)
    =⟨ ap (transport (EM H⊗G.abgroup) (+-comm (S m) (S n))) $
       ap (cpₕₕ'' H⊗G.abgroup m n) $
       app= (! (Susp^-fmap-∘ (m + n)
                             (EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap 2)
                             (∧-cp₁₁ G H))) $
       Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x ⟩
  (transport (EM H⊗G.abgroup) (+-comm (S m) (S n)) $
   cpₕₕ'' H⊗G.abgroup m n $
   Susp^-fmap (m + n) (EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap 2 ∘ ∧-cp₁₁ G H) $
   Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x)
    =⟨ ap (transport (EM H⊗G.abgroup) (+-comm (S m) (S n))) $
       ap (cpₕₕ'' H⊗G.abgroup m n) $
       app= (ap (Susp^-fmap (m + n)) (λ= (∧-cp₁₁-comm G H))) $
       Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x ⟩
  (transport (EM H⊗G.abgroup) (+-comm (S m) (S n)) $
   cpₕₕ'' H⊗G.abgroup m n $
   Susp^-fmap (m + n) (EM-neg H⊗G.abgroup 2 ∘ ∧-cp₁₁ H G ∘ ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) $
   Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x)
    =⟨ app= (! (transp-naturality (λ {k} → cond-neg H⊗G.abgroup k (odd n)) (+-comm (S m) (S n)))) $
       transport (EM H⊗G.abgroup) (! (+-βr (S m) n)) $
       EM2-Susp H⊗G.abgroup (m + n) $
       Susp^-fmap (m + n) (EM-neg H⊗G.abgroup 2 ∘ ∧-cp₁₁ H G ∘ ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) $
       Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x ⟩
  (cond-neg H⊗G.abgroup (S n + S m) (odd n) $
   transport (EM H⊗G.abgroup) (+-comm (S m) (S n)) $
   transport (EM H⊗G.abgroup) (! (+-βr (S m) n)) $
   EM2-Susp H⊗G.abgroup (m + n) $
   Susp^-fmap (m + n) (EM-neg H⊗G.abgroup 2 ∘ ∧-cp₁₁ H G ∘ ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) $
   Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x)
    =⟨ ap (cond-neg H⊗G.abgroup (S n + S m) (odd n)) $
       ! $ transp-∙ {B = EM H⊗G.abgroup} (! (+-βr (S m) n)) (+-comm (S m) (S n)) $
       EM2-Susp H⊗G.abgroup (m + n) $
       Susp^-fmap (m + n) (EM-neg H⊗G.abgroup 2 ∘ ∧-cp₁₁ H G ∘ ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) $
       Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x ⟩
  (cond-neg H⊗G.abgroup (S n + S m) (odd n) $
   transport (EM H⊗G.abgroup) (! (+-βr (S m) n) ∙ +-comm (S m) (S n)) $
   EM2-Susp H⊗G.abgroup (m + n) $
   Susp^-fmap (m + n) (EM-neg H⊗G.abgroup 2 ∘ ∧-cp₁₁ H G ∘ ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) $
   Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x)
    =⟨ ap (cond-neg H⊗G.abgroup (S n + S m) (odd n)) $
       app= (ap (transport (EM H⊗G.abgroup))
                (set-path ℕ-level (! (+-βr (S m) n) ∙ +-comm (S m) (S n))
                                  (ap (λ k → S (S k)) (+-comm m n) ∙ ! (+-βr (S n) m)))) $
       EM2-Susp H⊗G.abgroup (m + n) $
       Susp^-fmap (m + n) (EM-neg H⊗G.abgroup 2 ∘ ∧-cp₁₁ H G ∘ ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) $
       Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x ⟩
  (cond-neg H⊗G.abgroup (S n + S m) (odd n) $
   transport (EM H⊗G.abgroup) (ap (λ k → S (S k)) (+-comm m n) ∙ ! (+-βr (S n) m)) $
   EM2-Susp H⊗G.abgroup (m + n) $
   Susp^-fmap (m + n) (EM-neg H⊗G.abgroup 2 ∘ ∧-cp₁₁ H G ∘ ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) $
   Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x)
    =⟨ ap (cond-neg H⊗G.abgroup (S n + S m) (odd n)) $
       transp-∙ {B = EM H⊗G.abgroup} (ap (λ k → S (S k)) (+-comm m n)) (! (+-βr (S n) m)) $
       EM2-Susp H⊗G.abgroup (m + n) $
       Susp^-fmap (m + n) (EM-neg H⊗G.abgroup 2 ∘ ∧-cp₁₁ H G ∘ ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) $
       Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x ⟩
  (cond-neg H⊗G.abgroup (S n + S m) (odd n) $
   transport (EM H⊗G.abgroup) (! (+-βr (S n) m)) $
   transport (EM H⊗G.abgroup) (ap (λ k → S (S k)) (+-comm m n)) $
   EM2-Susp H⊗G.abgroup (m + n) $
   Susp^-fmap (m + n) (EM-neg H⊗G.abgroup 2 ∘ ∧-cp₁₁ H G ∘ ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) $
   Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x)
    =⟨ ap (cond-neg H⊗G.abgroup (S n + S m) (odd n)) $
       ap (transport (EM H⊗G.abgroup) (! (+-βr (S n) m))) $
       app= (ap coe (∘-ap (EM H⊗G.abgroup) (λ k → S (S k)) (+-comm m n))) $
       EM2-Susp H⊗G.abgroup (m + n)  $
       Susp^-fmap (m + n) (EM-neg H⊗G.abgroup 2 ∘ ∧-cp₁₁ H G ∘ ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) $
       Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x ⟩
  (cond-neg H⊗G.abgroup (S n + S m) (odd n) $
   transport (EM H⊗G.abgroup) (! (+-βr (S n) m)) $
   transport (λ k → EM H⊗G.abgroup (S (S k))) (+-comm m n) $
   EM2-Susp H⊗G.abgroup (m + n) $
   Susp^-fmap (m + n) (EM-neg H⊗G.abgroup 2 ∘ ∧-cp₁₁ H G ∘ ∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) $
   Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x)
    =⟨ ap (cond-neg H⊗G.abgroup (S n + S m) (odd n)) $
       ap (transport (EM H⊗G.abgroup) (! (+-βr (S n) m))) $
       ap (transport (λ k → EM H⊗G.abgroup (S (S k))) (+-comm m n)) $
       ap (EM2-Susp H⊗G.abgroup (m + n)) $
       app= (Susp^-fmap-∘ (m + n) (EM-neg H⊗G.abgroup 2 ∘ ∧-cp₁₁ H G) (∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp))) $
       Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x ⟩
  (cond-neg H⊗G.abgroup (S n + S m) (odd n) $
   transport (EM H⊗G.abgroup) (! (+-βr (S n) m)) $
   transport (λ k → EM H⊗G.abgroup (S (S k))) (+-comm m n) $
   EM2-Susp H⊗G.abgroup (m + n) $
   Susp^-fmap (m + n) (EM-neg H⊗G.abgroup 2 ∘ ∧-cp₁₁ H G) $
   Susp^-fmap (m + n) (∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) $
   Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x)
    =⟨ ap (cond-neg H⊗G.abgroup (S n + S m) (odd n)) $
       ap (transport (EM H⊗G.abgroup) (! (+-βr (S n) m))) $
       app= (! (transp-naturality
                  (λ {k} → EM2-Susp H⊗G.abgroup k ∘
                           Susp^-fmap k (EM-neg H⊗G.abgroup 2 ∘ ∧-cp₁₁ H G))
                  (+-comm m n))) $
       Susp^-fmap (m + n) (∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) $
       Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x ⟩
  (cond-neg H⊗G.abgroup (S n + S m) (odd n) $
   transport (EM H⊗G.abgroup) (! (+-βr (S n) m)) $
   EM2-Susp H⊗G.abgroup (n + m) $
   Susp^-fmap (n + m) (EM-neg H⊗G.abgroup 2 ∘ ∧-cp₁₁ H G) $
   transport (λ k → Susp^ k (⊙EM₁ H.grp ∧ ⊙EM₁ G.grp)) (+-comm m n) $
   Susp^-fmap (m + n) (∧-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp)) $
   Σ^∧Σ^-out (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x)
    =⟨ ap (cond-neg H⊗G.abgroup (S n + S m) (odd n)) $
       ap (transport (EM H⊗G.abgroup) (! (+-βr (S n) m))) $
       ap (EM2-Susp H⊗G.abgroup (n + m)) $
       ap (Susp^-fmap (n + m) (EM-neg H⊗G.abgroup 2 ∘ ∧-cp₁₁ H G)) $
       Σ^∧Σ^-out-swap (⊙EM₁ G.grp) (⊙EM₁ H.grp) m n x ⟩
  (cond-neg H⊗G.abgroup (S n + S m) (odd n) $
   transport (EM H⊗G.abgroup) (! (+-βr (S n) m)) $
   EM2-Susp H⊗G.abgroup (n + m) $
   Susp^-fmap (n + m) (EM-neg H⊗G.abgroup 2 ∘ ∧-cp₁₁ H G) $
   maybe-Susp^-flip (n + m) (and (odd n) (odd m)) $
   Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
   ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x)
    =⟨ ap (cond-neg H⊗G.abgroup (S n + S m) (odd n)) $
       ap (transport (EM H⊗G.abgroup) (! (+-βr (S n) m))) $
       ap (EM2-Susp H⊗G.abgroup (n + m)) $
       app= (Susp^-fmap-∘ (n + m) (EM-neg H⊗G.abgroup 2) (∧-cp₁₁ H G)) $
       maybe-Susp^-flip (n + m) (and (odd n) (odd m)) $
       Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
       ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x ⟩
  (cond-neg H⊗G.abgroup (S n + S m) (odd n) $
   transport (EM H⊗G.abgroup) (! (+-βr (S n) m)) $
   EM2-Susp H⊗G.abgroup (n + m) $
   Susp^-fmap (n + m) (EM-neg H⊗G.abgroup 2) $
   Susp^-fmap (n + m) (∧-cp₁₁ H G) $
   maybe-Susp^-flip (n + m) (and (odd n) (odd m)) $
   Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
   ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x)
    =⟨ ap (cond-neg H⊗G.abgroup (S n + S m) (odd n)) $
       ap (transport (EM H⊗G.abgroup) (! (+-βr (S n) m))) $
       ap (EM2-Susp H⊗G.abgroup (n + m)) $
       ap (Susp^-fmap (n + m) (EM-neg H⊗G.abgroup 2)) $
       maybe-Susp^-flip-natural (∧-cp₁₁ H G) (n + m) (and (odd n) (odd m)) $
       Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
       ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x ⟩
  (cond-neg H⊗G.abgroup (S n + S m) (odd n) $
   transport (EM H⊗G.abgroup) (! (+-βr (S n) m)) $
   EM2-Susp H⊗G.abgroup (n + m) $
   Susp^-fmap (n + m) (EM-neg H⊗G.abgroup 2) $
   maybe-Susp^-flip (n + m) (and (odd n) (odd m)) $
   Susp^-fmap (n + m) (∧-cp₁₁ H G) $
   Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
   ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x)
    =⟨ ap (cond-neg H⊗G.abgroup (S n + S m) (odd n)) $
       ap (transport (EM H⊗G.abgroup) (! (+-βr (S n) m))) $
       ap (EM2-Susp H⊗G.abgroup (n + m)) $
       app= (! p₂) $
       maybe-Susp^-flip (n + m) (and (odd n) (odd m)) $
       Susp^-fmap (n + m) (∧-cp₁₁ H G) $
       Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
       ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x ⟩
  (cond-neg H⊗G.abgroup (S n + S m) (odd n) $
   transport (EM H⊗G.abgroup) (! (+-βr (S n) m)) $
   EM2-Susp H⊗G.abgroup (n + m) $
   transport (λ K → Susp^ (n + m) (EM K 2)) (inv-path H⊗G.abgroup) $
   maybe-Susp^-flip (n + m) (and (odd n) (odd m)) $
   Susp^-fmap (n + m) (∧-cp₁₁ H G) $
   Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
   ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x)
    =⟨ ap (cond-neg H⊗G.abgroup (S n + S m) (odd n)) $
       app= (transp-naturality (λ {K} → transport (EM K) (! (+-βr (S n) m)) ∘ EM2-Susp K (n + m))
                               (inv-path H⊗G.abgroup)) $
       maybe-Susp^-flip (n + m) (and (odd n) (odd m)) $
       Susp^-fmap (n + m) (∧-cp₁₁ H G) $
       Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
       ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x ⟩
  (cond-neg H⊗G.abgroup (S n + S m) (odd n) $
   transport (λ K → EM K (S n + S m)) (inv-path H⊗G.abgroup) $
   transport (EM H⊗G.abgroup) (! (+-βr (S n) m)) $
   EM2-Susp H⊗G.abgroup (n + m) $
   maybe-Susp^-flip (n + m) (and (odd n) (odd m)) $
   Susp^-fmap (n + m) (∧-cp₁₁ H G) $
   Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
   ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x)
    =⟨ ap (cond-neg H⊗G.abgroup (S n + S m) (odd n)) $
       ap (transport (λ K → EM K (S n + S m)) (inv-path H⊗G.abgroup)) $
       ap (transport (EM H⊗G.abgroup) (! (+-βr (S n) m))) $
       EM2-Susp-maybe-Susp^-flip H⊗G.abgroup (n + m) (and (odd n) (odd m)) h₁ $
       Susp^-fmap (n + m) (∧-cp₁₁ H G) $
       Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
       ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x ⟩
  (cond-neg H⊗G.abgroup (S n + S m) (odd n) $
   transport (λ K → EM K (S n + S m)) (inv-path H⊗G.abgroup) $
   transport (EM H⊗G.abgroup) (! (+-βr (S n) m)) $
   Trunc-fmap (maybe-Susp^-flip (S n + m) (and (odd n) (odd m))) $
   EM2-Susp H⊗G.abgroup (n + m) $
   Susp^-fmap (n + m) (∧-cp₁₁ H G) $
   Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
   ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x)
    =⟨ ap (cond-neg H⊗G.abgroup (S n + S m) (odd n)) $
       ap (transport (λ K → EM K (S n + S m)) (inv-path H⊗G.abgroup)) $
       ap (transport (EM H⊗G.abgroup) (! (+-βr (S n) m))) $
       maybe-Susp^-flip-cond-neg H⊗G.abgroup (S n + m) (and (odd n) (odd m)) h₂ $
       EM2-Susp H⊗G.abgroup (n + m) $
       Susp^-fmap (n + m) (∧-cp₁₁ H G) $
       Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
       ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x ⟩
  (cond-neg H⊗G.abgroup (S n + S m) (odd n) $
   transport (λ K → EM K (S n + S m)) (inv-path H⊗G.abgroup) $
   transport (EM H⊗G.abgroup) (! (+-βr (S n) m)) $
   cond-neg H⊗G.abgroup (S (S n + m)) (and (odd n) (odd m)) $
   EM2-Susp H⊗G.abgroup (n + m) $
   Susp^-fmap (n + m) (∧-cp₁₁ H G) $
   Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
   ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x)
    =⟨ ap (cond-neg H⊗G.abgroup (S n + S m) (odd n)) $
       ap (transport (λ K → EM K (S n + S m)) (inv-path H⊗G.abgroup)) $
       app= (! (transp-naturality (λ {k} → cond-neg H⊗G.abgroup k (and (odd n) (odd m))) (! (+-βr (S n) m)))) $
       EM2-Susp H⊗G.abgroup (n + m) $
       Susp^-fmap (n + m) (∧-cp₁₁ H G) $
       Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
       ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x ⟩
  (cond-neg H⊗G.abgroup (S n + S m) (odd n) $
   transport (λ K → EM K (S n + S m)) (inv-path H⊗G.abgroup) $
   cond-neg H⊗G.abgroup (S n + S m) (and (odd n) (odd m)) $
   transport (EM H⊗G.abgroup) (! (+-βr (S n) m)) $
   EM2-Susp H⊗G.abgroup (n + m) $
   Susp^-fmap (n + m) (∧-cp₁₁ H G) $
   Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
   ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x)
    =⟨ ap (cond-neg H⊗G.abgroup (S n + S m) (odd n)) $
       cond-neg-∘ H⊗G.abgroup (S n + S m) true (and (odd n) (odd m)) $
       transport (EM H⊗G.abgroup) (! (+-βr (S n) m)) $
       EM2-Susp H⊗G.abgroup (n + m) $
       Susp^-fmap (n + m) (∧-cp₁₁ H G) $
       Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
       ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x ⟩
  (cond-neg H⊗G.abgroup (S n + S m) (odd n) $
   cond-neg H⊗G.abgroup (S n + S m) (negate (and (odd n) (odd m))) $
   transport (EM H⊗G.abgroup) (! (+-βr (S n) m)) $
   EM2-Susp H⊗G.abgroup (n + m) $
   Susp^-fmap (n + m) (∧-cp₁₁ H G) $
   Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
   ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x)
    =⟨ cond-neg-∘ H⊗G.abgroup (S n + S m) (odd n) (negate (and (odd n) (odd m))) $
       transport (EM H⊗G.abgroup) (! (+-βr (S n) m)) $
       EM2-Susp H⊗G.abgroup (n + m) $
       Susp^-fmap (n + m) (∧-cp₁₁ H G) $
       Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
       ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x ⟩
  (cond-neg H⊗G.abgroup (S n + S m) (xor (odd n) (negate (and (odd n) (odd m)))) $
   transport (EM H⊗G.abgroup) (! (+-βr (S n) m)) $
   EM2-Susp H⊗G.abgroup (n + m) $
   Susp^-fmap (n + m) (∧-cp₁₁ H G) $
   Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
   ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x)
    =⟨ app= (ap (cond-neg H⊗G.abgroup (S n + S m)) (bp (odd n) (odd m))) $
       transport (EM H⊗G.abgroup) (! (+-βr (S n) m)) $
       EM2-Susp H⊗G.abgroup (n + m) $
       Susp^-fmap (n + m) (∧-cp₁₁ H G) $
       Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
       ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x ⟩
  (cond-neg H⊗G.abgroup (S n + S m) (xor (and (odd (S m)) (odd (S n))) (odd m)) $
   transport (EM H⊗G.abgroup) (! (+-βr (S n) m)) $
   EM2-Susp H⊗G.abgroup (n + m) $
   Susp^-fmap (n + m) (∧-cp₁₁ H G) $
   Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
   ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x)
    =⟨ ! $ cond-neg-∘ H⊗G.abgroup (S n + S m) (and (odd (S m)) (odd (S n))) (odd m) $
       transport (EM H⊗G.abgroup) (! (+-βr (S n) m)) $
       EM2-Susp H⊗G.abgroup (n + m) $
       Susp^-fmap (n + m) (∧-cp₁₁ H G) $
       Σ^∧Σ^-out (⊙EM₁ H.grp) (⊙EM₁ G.grp) n m $
       ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x ⟩
  (cond-neg H⊗G.abgroup (S n + S m) (and (odd (S m)) (odd (S n))) $
   cpₕₕ' H G n m $
   ∧-swap (⊙Susp^ m (⊙EM₁ G.grp)) (⊙Susp^ n (⊙EM₁ H.grp)) x) =∎
  where
    p₁ : transport (λ K → Susp^ (m + n) (EM K 2)) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative)
         == Susp^-fmap (m + n) (EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap 2)
    p₁ =
      transport (λ K → Susp^ (m + n) (EM K 2)) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative)
        =⟨ ap coe (ap-∘ (Susp^ (m + n)) (λ K → EM K 2) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative)) ⟩
      transport (Susp^ (m + n)) (ap (λ K → EM K 2) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative))
        =⟨ transport-Susp^ (m + n) (ap (λ K → EM K 2) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative)) ⟩
      Susp^-fmap (m + n) (transport (λ K → EM K 2) (uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative))
        =⟨ ap (Susp^-fmap (m + n)) (transport-EM-uaᴬᴳ G⊗H.abgroup H⊗G.abgroup G⊗H.commutative 2) ⟩
      Susp^-fmap (m + n) (EM-fmap G⊗H.abgroup H⊗G.abgroup G⊗H.swap 2) =∎
    p₂ : transport (λ K → Susp^ (n + m) (EM K 2)) (inv-path H⊗G.abgroup)
         == Susp^-fmap (n + m) (EM-neg H⊗G.abgroup 2)
    p₂ =
      transport (λ K → Susp^ (n + m) (EM K 2)) (inv-path H⊗G.abgroup)
        =⟨ ap coe (ap-∘ (Susp^ (n + m)) (λ K → EM K 2) (inv-path H⊗G.abgroup)) ⟩
      transport (Susp^ (n + m)) (ap (λ K → EM K 2) (inv-path H⊗G.abgroup))
        =⟨ transport-Susp^ (n + m) (ap (λ K → EM K 2) (inv-path H⊗G.abgroup)) ⟩
      Susp^-fmap (n + m) (transport (λ K → EM K 2) (inv-path H⊗G.abgroup))
        =⟨ ap (Susp^-fmap (n + m)) (transport-EM-uaᴬᴳ H⊗G.abgroup H⊗G.abgroup (inv-iso H⊗G.abgroup) 2) ⟩
      Susp^-fmap (n + m) (EM-neg H⊗G.abgroup 2) =∎
    h₁ : n + m == 0 → and (odd n) (odd m) == false
    h₁ p = ap (λ k → and (odd k) (odd m)) (fst (+-0 n m p))
    h₂ : S (n + m) == 0 → and (odd n) (odd m) == inr unit
    h₂ p = ⊥-elim (ℕ-S≠O (n + m) p)
    bp : ∀ (b c : Bool) → xor b (negate (and b c)) == xor (and (negate c) (negate b)) c
    bp true  true  = idp
    bp true  false = idp
    bp false true  = idp
    bp false false = idp
