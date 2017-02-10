{-# OPTIONS --without-K --rewriting #-}

open import HoTT
open import cw.CW
open import homotopy.PinSn
open import cw.SphereEndomorphism

module cw.DegreeBySquashing where

  module DegreeAboveOne {i} {n : ℕ} (skel : Skeleton {i} (S (S n)))
    (skel-has-dec-cells : has-cells-with-dec-eq skel)
    -- the cells at the upper and lower dimensions
    (upper : cells-last skel)
    (lower : cells-last (cw-init skel))
    where

    private
      lower-skel = cw-init skel
      lower-cells = cells-last lower-skel
      lower-cells-has-dec-eq = snd (fst skel-has-dec-cells)

    -- squash the lower CW complex except one of its cells [lower]
    cw-squash-lower-to-Sphere : ⟦ lower-skel ⟧ → Sphere (S n)
    cw-squash-lower-to-Sphere = Attached-rec (λ _ → north) squash-hubs squash-spokes where
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
    degree-map = cw-squash-lower-to-Sphere ∘ attaching-last skel upper

    degree-map' : ℤ-group →ᴳ ℤ-group
    degree-map' = –>ᴳ (πS-SphereS-iso-ℤ n)
               ∘ᴳ Trunc-rec →ᴳ-level (πS-fmap n)
                    (⊙SphereS-endo-in n [ degree-map ])
               ∘ᴳ <–ᴳ (πS-SphereS-iso-ℤ n)

    degree' : ℤ → ℤ
    degree' = GroupHom.f degree-map'

    degree : ℤ
    degree = degree' 1

  module DegreeAtOne {i} (skel : Skeleton {i} 1)
    (skel-has-dec-cells : has-cells-with-dec-eq skel)
    -- the cells at the upper and lower dimensions
    (line : cells-last skel)
    (point : cells-last (cw-init skel)) where

    private
      points-dec-eq = fst skel-has-dec-cells
      endpoint = attaching-last skel

    -- Maybe [true] can or should be mapped to [-1]. Not sure.
    degree : ℤ
    degree with points-dec-eq (endpoint line true) point
    degree | inl _ = 1
    degree | inr _ with points-dec-eq (endpoint line false) point
    degree | inr _ | inl _ = -1
    degree | inr _ | inr _ = 0

  degree : ∀ {i} {n} (skel : Skeleton {i} (S n))
    (skel-has-dec-cells : has-cells-with-dec-eq skel)
    (upper : cells-last skel)
    (lower : cells-last (cw-init skel))
    → ℤ
  degree {n = O} = DegreeAtOne.degree
  degree {n = S _} = DegreeAboveOne.degree
