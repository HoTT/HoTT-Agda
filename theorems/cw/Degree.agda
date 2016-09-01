{-# OPTIONS --without-K #-}

open import HoTT
open import cw.CW
open import homotopy.PinSn
open import cw.SphereEndomorphism

module cw.Degree where

  pointed-degree-map-to-degree-map : ∀ n
    → fst (⊙Trunc 0 (⊙Sphere (S n) ⊙→ ⊙Sphere (S n)))
    → Trunc 0 (Sphere (S n) → Sphere (S n))
  pointed-degree-map-to-degree-map n = Trunc-rec Trunc-level ([_] ∘ fst)

  postulate
    -- true, but not the main part of the cohomology argument
    -- TODO Prove this!
    pointed-degree-map-to-degree-map-is-equiv :
      ∀ n → is-equiv (pointed-degree-map-to-degree-map n)

  pointed-degree-map-equiv-degree-map : ∀ n
    → fst (⊙Trunc 0 (⊙Sphere (S n) ⊙→ ⊙Sphere (S n)))
    ≃ Trunc 0 (Sphere (S n) → Sphere (S n))
  pointed-degree-map-equiv-degree-map n =
    _ , pointed-degree-map-to-degree-map-is-equiv n

  module _ {i} {n : ℕ} (skel : Skeleton {i} (S (S n)))
    (skel-has-dec-cells : has-dec-cells skel)
    -- the cells at the upper and lower dimensions
    (upper : cells-last skel)
    (lower : cells-nth (inr ltS) skel)
    where

    private
      lower-skel = cw-take (inr ltS) skel
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
                    (<– (pointed-degree-map-equiv-degree-map n) [ degree-map ])
               ∘ᴳ <–ᴳ (πS-SphereS-iso-ℤ n)

    degree' : ℤ → ℤ
    degree' = GroupHom.f degree-map'

    degree : ℤ
    degree = degree' 1
