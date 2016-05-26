{-# OPTIONS --without-K #-}

open import HoTT
open import cw.CW

module cw.Degree where

trivial-boundary : ∀ {i} (n : ℕ) (X : Type i)
  → Boundry Unit X (Sphere₋₁ {i} n)
trivial-boundary _ _ _ _ = tt

cw-degree-map-top : ∀ {i} {n : ℕ} (skel : Skeleton {i} n)
  → ⟦ skel ⟧ → Attach (trivial-boundary n (cw-cells-top skel))
cw-degree-map-top {n = O}   skel               c = hub c
cw-degree-map-top {n = S n} (skel , cells , b) =
  Attach-rec (λ _ → incl tt) hub spoke

cw-degree-map : ∀ {i} {n m : ℕ} (m≤n : m ≤ n) (skel : Skeleton {i} n)
  → ⟦ cw-take m≤n skel ⟧ → Attach (trivial-boundary m (cw-cells m≤n skel))
cw-degree-map m≤n = cw-degree-map-top ∘ cw-take m≤n
