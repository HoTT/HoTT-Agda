{-# OPTIONS --without-K #-}

open import HoTT
open import cw.CW

module cw.Degree
  {i} {n : ℕ} (skel : Skeleton {i} (S (S n)))
  (dec : has-dec-eq (cw-cells (inr ltS) skel))
  (upper : cw-cells-top skel) → (lower : cw-cells (inr ltS) skel) where

private
  lower-skel = cw-take (inr ltS) skel

cw-degree-map : Sphere {i} (S n) → Sphere {i} (S n)
cw-degree-map =
  Attach-rec (λ _ → north _) squash-hubs squash-spokes ∘ cw-boundary-top skel upper
    where
      squash-hubs : cw-cells-top lower-skel → Sphere {i} (S n)
      squash-hubs c with dec c lower
      ... | (inl _) = south _
      ... | (inr _) = north _

      squash-spokes : (c : cw-cells-top lower-skel) → Sphere {i} n
        → north (Sphere {i} n) == squash-hubs c
      squash-spokes c s with dec c lower
      ... | (inl _) = merid _ s
      ... | (inr _) = idp

