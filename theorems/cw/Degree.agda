{-# OPTIONS --without-K #-}

open import HoTT
open import cw.CW
open import homotopy.PinSn

module cw.Degree
  {i} {n : ℕ} (skel : Skeleton {i} (S (S n)))
  (skel-has-dec-cells : has-dec-cells skel)
  (skel-is-aligned : is-aligned skel)
  -- the cells at the upper and lower dimensions
  (upper : cells-last skel)
  (lower : cells-at (inr ltS) skel)
  where

private
  lower-skel = cw-take (inr ltS) skel
  lower-cells = cells-last lower-skel
  lower-cells-has-dec-eq = snd (fst skel-has-dec-cells)

-- squash the lower CW complex except one of its cells [lower]
cw-squash-lower-to-Sphere : ⟦ lower-skel ⟧ → Sphere (S n)
cw-squash-lower-to-Sphere = Attach-rec (λ _ → north) squash-hubs squash-spokes where
  -- squash cells except [lower]
  squash-hubs : lower-cells → Sphere (S n)
  squash-hubs c with lower-cells-has-dec-eq c lower
  ... | (inl _) = south
  ... | (inr _) = north
  -- squash cells except [lower]
  squash-spokes : (c : lower-cells) → Sphere n
    → north == squash-hubs c
  squash-spokes c s with lower-cells-has-dec-eq c lower
  ... | (inl _) = merid s
  ... | (inr _) = idp

degree-map : Sphere (S n) → Sphere (S n)
degree-map = cw-squash-lower-to-Sphere ∘ boundary-last skel upper

degree-⊙map : fst (⊙Sphere (S n) ⊙→ ⊙Sphere (S n))
degree-⊙map = degree-map , ap cw-squash-lower-to-Sphere (! (snd (snd skel-is-aligned upper)))

degree' : ℤ → ℤ
degree' = transport Group.El (πₙ₊₁Sⁿ⁺¹ n)
        ∘ GroupHom.f (πS-fmap n degree-⊙map)
        ∘ transport! Group.El (πₙ₊₁Sⁿ⁺¹ n)

degree : ℤ
degree = degree' 1
