{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import homotopy.EilenbergMacLane

module cohomology.CupProduct.OnEM.InLowDegrees2 {i} {j} (G : AbGroup i) (H : AbGroup j) where

private
  module G = AbGroup G
  module H = AbGroup H
  module G⊗H = TensorProduct G H

open EMExplicit G⊗H.abgroup
open import cohomology.CupProduct.OnEM.InLowDegrees G H public
open import cohomology.CupProduct.OnEM.CommutativityInLowDegrees
open CP₁₁-comm G H

cp₁₁-embase-r : (x : EM₁ G.grp) → cp₁₁ x embase == [ north ]₂
cp₁₁-embase-r x = CP₁₁Comm.f x embase

module ∧-cp₁₁-Rec =
  SmashRec {X = ⊙EM₁ G.grp} {Y = ⊙EM₁ H.grp} {C = EM 2}
            cp₁₁
            [ north ]₂ [ north ]₂
            cp₁₁-embase-r
            (λ y → idp)

∧-cp₁₁ : ⊙EM₁ G.grp ∧ ⊙EM₁ H.grp → EM 2
∧-cp₁₁ = ∧-cp₁₁-Rec.f

⊙∧-cp₁₁ : ⊙EM₁ G.grp ⊙∧ ⊙EM₁ H.grp ⊙→ ⊙EM 2
⊙∧-cp₁₁ = ∧-cp₁₁-Rec.f , idp
