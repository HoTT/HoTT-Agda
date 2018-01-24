{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.FinWedge

module homotopy.Bouquet {i} where

Rose : (I : Type i) → Type i
Rose I = BigWedge {A = I} (λ _ → ⊙S¹)

FinBouquetLift-family : (I m : ℕ) → (Fin I → Ptd i)
FinBouquetLift-family I m _ = ⊙Lift {j = i} (⊙Sphere m)

⊙FinBouquetLift : (I m : ℕ) → Ptd i
⊙FinBouquetLift I m = ⊙FinWedge (FinBouquetLift-family I m)
