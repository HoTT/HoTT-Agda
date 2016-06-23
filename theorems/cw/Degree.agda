{-# OPTIONS --without-K #-}

open import HoTT
open import cw.CW
open import homotopy.PinSn

module cw.Degree
  {i} {n : ℕ} (skel : Skeleton {i} (S (S n)))
  (dec : has-dec-eq (cw-cells (inr ltS) skel))
  (upper : cw-cells-top skel) (lower : cw-cells (inr ltS) skel) where

private
  lower-skel = cw-take (inr ltS) skel

cw-degree-map : Sphere (S n) → Sphere (S n)
cw-degree-map =
  Attach-rec (λ _ → north) squash-hubs squash-spokes ∘ cw-boundary-top skel upper
    where
      squash-hubs : cw-cells-top lower-skel → Sphere (S n)
      squash-hubs c with dec c lower
      ... | (inl _) = south
      ... | (inr _) = north

      squash-spokes : (c : cw-cells-top lower-skel) → Sphere n
        → north == squash-hubs c
      squash-spokes c s with dec c lower
      ... | (inl _) = merid s
      ... | (inr _) = idp
