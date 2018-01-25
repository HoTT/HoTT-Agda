{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.FinWedge

module homotopy.Bouquet where

Rose : ∀ {i} (I : Type i) → Type i
Rose I = BigWedge {A = I} (λ _ → ⊙S¹)

FinBouquetLift-family : ∀ {i} (I m : ℕ) → (Fin I → Ptd i)
FinBouquetLift-family {i} I m _ = ⊙Lift {j = i} (⊙Sphere m)

⊙FinBouquetLift : ∀ {i} (I m : ℕ) → Ptd i
⊙FinBouquetLift I m = ⊙FinWedge (FinBouquetLift-family I m)

FinBouquet-family : (I m : ℕ) → (Fin I → Ptd₀)
FinBouquet-family I m _ = ⊙Sphere m

⊙FinBouquet : (I m : ℕ) → Ptd₀
⊙FinBouquet I m = ⊙FinWedge (FinBouquet-family I m)
